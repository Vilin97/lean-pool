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

/-! # V37: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_445 :
    ((765842864606636857627 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(234493277614459757331 / 312500000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6830540250086371 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ))) -
              6 * (546814399689969324883 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (933125602161 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (933125602161 / 2000000000000 : ℝ)) =
      Real.log (2933125602161 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((933125602161 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (944375602161 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (765842864606636857627 / 2000000000000000000000 : ℝ) ≤
      Real.log (2933125602161 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (944375602161 / 2000000000000 : ℝ) ≤
      (-(234493277614459757331 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (944375602161 / 2000000000000 : ℝ) = (944375602161 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (944375602161 / 500000000000 : ℝ) ≤
            (198723710073040242669 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6830540250086371 / 10000000000000000 : ℝ) ≤ Real.sqrt (933125602161 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (933125602161 / 2000000000000 : ℝ) ≤ (3415270125043187 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (933125602161 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau662 :
    Real.arctan (3415270125043187 / 11055086293936074 : ℝ) ≤
      (2996310293174500557039 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau661 :
    Real.arctan (3415270125043187 / 5000000000000000 : ℝ) ≤
      (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3027543146968037 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3415270125043187 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3415270125043187 / 5000000000000000 : ℝ) /
                (1 + (3027543146968037 / 2500000000000000 : ℝ)) =
              (3415270125043187 / 11055086293936074 : ℝ)
            by
        norm_num];
        exact hau662)
  have hat1 :
    (Real.pi / 2 - (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3415270125043187 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3415270125043187 : ℝ) =
              (3415270125043187 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau661)
  have hz1 :
    (5000000000000000 / 3415270125043187 : ℝ) ≤
      1 / Real.sqrt (933125602161 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3415270125043187 : ℝ) = 1 / (3415270125043187 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6830540250086371 : ℝ) ≤
      (546814399689969324883 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (933125602161 / 2000000000000 : ℝ) ≤
      (750000000000000 / 6830540250086371 : ℝ) := by
    rw [show
        (750000000000000 / 6830540250086371 : ℝ) =
          (3 / 40) / (6830540250086371 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ))) -
        6 * (546814399689969324883 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (933125602161 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (933125602161 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6830540250086371 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ))) -
          6 * (546814399689969324883 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (933125602161 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (933125602161 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (933125602161 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_446 :
    ((3838240205298106251957 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(747577809759293719037 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1710056835599697 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (599922291000491826411 / 2000000000000000000000 : ℝ))) -
              6 * (218418460430541568817 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (467887100957 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (467887100957 / 1000000000000 : ℝ)) =
      Real.log (1467887100957 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((467887100957 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (473512100957 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3838240205298106251957 / 10000000000000000000000 : ℝ) ≤
      Real.log (1467887100957 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (473512100957 / 1000000000000 : ℝ) ≤
      (-(747577809759293719037 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (473512100957 / 1000000000000 : ℝ) = (473512100957 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (473512100957 / 250000000000 : ℝ) ≤
            (638716550840706280963 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1710056835599697 / 2500000000000000 : ℝ) ≤ Real.sqrt (467887100957 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (467887100957 / 1000000000000 : ℝ) ≤ (6840227342398791 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (467887100957 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau664 :
    Real.arctan (207279616436327 / 670170880935590 : ℝ) ≤
      (599922291000491826411 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau663 :
    Real.arctan (6840227342398791 / 10000000000000000 : ℝ) ≤
      (2 * (599922291000491826411 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1211563907087447 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6840227342398791 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6840227342398791 / 10000000000000000 : ℝ) /
                (1 + (1211563907087447 / 1000000000000000 : ℝ)) =
              (207279616436327 / 670170880935590 : ℝ)
            by
        norm_num];
        exact hau664)
  have hat1 :
    (Real.pi / 2 - (2 * (599922291000491826411 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6840227342398791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6840227342398791 : ℝ) =
              (6840227342398791 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau663)
  have hz1 :
    (10000000000000000 / 6840227342398791 : ℝ) ≤
      1 / Real.sqrt (467887100957 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6840227342398791 : ℝ) =
          1 / (6840227342398791 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 570018945199899 : ℝ) ≤
      (218418460430541568817 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (467887100957 / 1000000000000 : ℝ) ≤
      (62500000000000 / 570018945199899 : ℝ) := by
    rw [show
        (62500000000000 / 570018945199899 : ℝ) =
          (3 / 40) / (1710056835599697 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (599922291000491826411 / 2000000000000000000000 : ℝ))) -
        6 * (218418460430541568817 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (467887100957 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (467887100957 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1710056835599697 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (599922291000491826411 / 2000000000000000000000 : ℝ))) -
          6 * (218418460430541568817 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (467887100957 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (467887100957 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (467887100957 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_447 :
    ((240453621765865922073 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7447849530514487331947 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1369980147058343 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (750726243913883062749 / 2500000000000000000000 : ℝ))) -
              6 * (218112452596585238241 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (938422801667 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (938422801667 / 2000000000000 : ℝ)) =
      Real.log (2938422801667 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((938422801667 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (949672801667 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (240453621765865922073 / 625000000000000000000 : ℝ) ≤
      Real.log (2938422801667 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (949672801667 / 2000000000000 : ℝ) ≤
      (-(7447849530514487331947 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (949672801667 / 2000000000000 : ℝ) = (949672801667 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (949672801667 / 500000000000 : ℝ) ≤
            (6415094075485512668053 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1369980147058343 / 2000000000000000 : ℝ) ≤ Real.sqrt (938422801667 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (938422801667 / 2000000000000 : ℝ) ≤ (3424950367645859 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (938422801667 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau666 :
    Real.arctan (3424950367645859 / 11060551544276931 : ℝ) ≤
      (750726243913883062749 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau665 :
    Real.arctan (3424950367645859 / 5000000000000000 : ℝ) ≤
      (2 * (750726243913883062749 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6060551544276931 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3424950367645859 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3424950367645859 / 5000000000000000 : ℝ) /
                (1 + (6060551544276931 / 5000000000000000 : ℝ)) =
              (3424950367645859 / 11060551544276931 : ℝ)
            by
        norm_num];
        exact hau666)
  have hat1 :
    (Real.pi / 2 - (2 * (750726243913883062749 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3424950367645859 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3424950367645859 : ℝ) =
              (3424950367645859 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau665)
  have hz1 :
    (5000000000000000 / 3424950367645859 : ℝ) ≤
      1 / Real.sqrt (938422801667 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3424950367645859 : ℝ) = 1 / (3424950367645859 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1369980147058343 : ℝ) ≤
      (218112452596585238241 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (938422801667 / 2000000000000 : ℝ) ≤
      (150000000000000 / 1369980147058343 : ℝ) := by
    rw [show
        (150000000000000 / 1369980147058343 : ℝ) =
          (3 / 40) / (1369980147058343 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (750726243913883062749 / 2500000000000000000000 : ℝ))) -
        6 * (218112452596585238241 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (938422801667 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (938422801667 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1369980147058343 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (750726243913883062749 / 2500000000000000000000 : ℝ))) -
          6 * (218112452596585238241 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (938422801667 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (938422801667 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (938422801667 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_448 :
    ((3856267566566845575453 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1854999686683688517279 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3429780243361081 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ))) -
              6 * (217807727351321952453 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (47053570071 / 100000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47053570071 / 100000000000 : ℝ)) =
      Real.log (147053570071 / 100000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47053570071 / 100000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (47616070071 / 100000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3856267566566845575453 / 10000000000000000000000 : ℝ) ≤
      Real.log (147053570071 / 100000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (47616070071 / 100000000000 : ℝ) ≤
      (-(1854999686683688517279 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (47616070071 / 100000000000 : ℝ) = (47616070071 / 25000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47616070071 / 25000000000 : ℝ) ≤
            (1610736214816311482721 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3429780243361081 / 5000000000000000 : ℝ) ≤ Real.sqrt (47053570071 / 100000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47053570071 / 100000000000 : ℝ) ≤ (1371912097344433 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47053570071 / 100000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau668 :
    Real.arctan (1371912097344433 / 4425312928848564 : ℝ) ≤
      (1503095444308757277833 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau667 :
    Real.arctan (1371912097344433 / 2000000000000000 : ℝ) ≤
      (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (606328232212141 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1371912097344433 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1371912097344433 / 2000000000000000 : ℝ) /
                (1 + (606328232212141 / 500000000000000 : ℝ)) =
              (1371912097344433 / 4425312928848564 : ℝ)
            by
        norm_num];
        exact hau668)
  have hat1 :
    (Real.pi / 2 - (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1371912097344433 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1371912097344433 : ℝ) =
              (1371912097344433 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau667)
  have hz1 :
    (2000000000000000 / 1371912097344433 : ℝ) ≤ 1 / Real.sqrt (47053570071 / 100000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1371912097344433 : ℝ) = 1 / (1371912097344433 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3429780243361081 : ℝ) ≤
      (217807727351321952453 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47053570071 / 100000000000 : ℝ) ≤
      (375000000000000 / 3429780243361081 : ℝ) := by
    rw [show
        (375000000000000 / 3429780243361081 : ℝ) =
          (3 / 40) / (3429780243361081 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ))) -
        6 * (217807727351321952453 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47053570071 / 100000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47053570071 / 100000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3429780243361081 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ))) -
          6 * (217807727351321952453 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (47053570071 / 100000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47053570071 / 100000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47053570071 / 100000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_449 :
    ((3865269074863888535449 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7392225314191339633631 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1717301663559907 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ))) -
              6 * (1087521378799764588307 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (943720001173 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (943720001173 / 2000000000000 : ℝ)) =
      Real.log (2943720001173 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((943720001173 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (954970001173 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3865269074863888535449 / 10000000000000000000000 : ℝ) ≤
      Real.log (2943720001173 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (954970001173 / 2000000000000 : ℝ) ≤
      (-(7392225314191339633631 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (954970001173 / 2000000000000 : ℝ) = (954970001173 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (954970001173 / 500000000000 : ℝ) ≤
            (6470718291808660366369 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1717301663559907 / 2500000000000000 : ℝ) ≤ Real.sqrt (943720001173 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (943720001173 / 2000000000000 : ℝ) ≤ (6869206654239631 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (943720001173 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau670 :
    Real.arctan (528400511864587 / 1702463364712795 : ℝ) ≤
      (3009469227143283066133 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau669 :
    Real.arctan (6869206654239631 / 10000000000000000 : ℝ) ≤
      (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2426404748253267 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6869206654239631 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6869206654239631 / 10000000000000000 : ℝ) /
                (1 + (2426404748253267 / 2000000000000000 : ℝ)) =
              (528400511864587 / 1702463364712795 : ℝ)
            by
        norm_num];
        exact hau670)
  have hat1 :
    (Real.pi / 2 - (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6869206654239631 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6869206654239631 : ℝ) =
              (6869206654239631 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau669)
  have hz1 :
    (10000000000000000 / 6869206654239631 : ℝ) ≤
      1 / Real.sqrt (943720001173 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6869206654239631 : ℝ) =
          1 / (6869206654239631 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1717301663559907 : ℝ) ≤
      (1087521378799764588307 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (943720001173 / 2000000000000 : ℝ) ≤
      (187500000000000 / 1717301663559907 : ℝ) := by
    rw [show
        (187500000000000 / 1717301663559907 : ℝ) =
          (3 / 40) / (1717301663559907 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ))) -
        6 * (1087521378799764588307 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (943720001173 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (943720001173 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1717301663559907 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ))) -
          6 * (1087521378799764588307 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (943720001173 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (943720001173 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (943720001173 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_450 :
    ((3874262487732329959907 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7364528804411839307839 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3439419647495053 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (753185006065245064909 / 2500000000000000000000 : ℝ))) -
              6 * (1086010444872883962773 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (473184300463 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (473184300463 / 1000000000000 : ℝ)) =
      Real.log (1473184300463 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((473184300463 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (478809300463 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3874262487732329959907 / 10000000000000000000000 : ℝ) ≤
      Real.log (1473184300463 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (478809300463 / 1000000000000 : ℝ) ≤
      (-(7364528804411839307839 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (478809300463 / 1000000000000 : ℝ) = (478809300463 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (478809300463 / 250000000000 : ℝ) ≤
            (6498414801588160692161 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3439419647495053 / 5000000000000000 : ℝ) ≤ Real.sqrt (473184300463 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (473184300463 / 1000000000000 : ℝ) ≤ (6878839294990109 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (473184300463 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau672 :
    Real.arctan (6878839294990109 / 22137480382941922 : ℝ) ≤
      (753185006065245064909 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau671 :
    Real.arctan (6878839294990109 / 10000000000000000 : ℝ) ≤
      (2 * (753185006065245064909 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6068740191470961 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6878839294990109 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6878839294990109 / 10000000000000000 : ℝ) /
                (1 + (6068740191470961 / 5000000000000000 : ℝ)) =
              (6878839294990109 / 22137480382941922 : ℝ)
            by
        norm_num];
        exact hau672)
  have hat1 :
    (Real.pi / 2 - (2 * (753185006065245064909 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6878839294990109 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6878839294990109 : ℝ) =
              (6878839294990109 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau671)
  have hz1 :
    (10000000000000000 / 6878839294990109 : ℝ) ≤
      1 / Real.sqrt (473184300463 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6878839294990109 : ℝ) =
          1 / (6878839294990109 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3439419647495053 : ℝ) ≤
      (1086010444872883962773 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (473184300463 / 1000000000000 : ℝ) ≤
      (375000000000000 / 3439419647495053 : ℝ) := by
    rw [show
        (375000000000000 / 3439419647495053 : ℝ) =
          (3 / 40) / (3439419647495053 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (753185006065245064909 / 2500000000000000000000 : ℝ))) -
        6 * (1086010444872883962773 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (473184300463 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (473184300463 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3439419647495053 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (753185006065245064909 / 2500000000000000000000 : ℝ))) -
          6 * (1086010444872883962773 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (473184300463 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (473184300463 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (473184300463 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_451 :
    ((776649563944038904551 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3668454396237089531377 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((215264327053751 / 312500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (754000828193542139837 / 2500000000000000000000 : ℝ))) -
              6 * (54225289558276524857 / 500000000000000000000 : ℝ)))) ≤
      Vfield (949017200679 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (949017200679 / 2000000000000 : ℝ)) =
      Real.log (2949017200679 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((949017200679 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (960267200679 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (776649563944038904551 / 2000000000000000000000 : ℝ) ≤
      Real.log (2949017200679 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (960267200679 / 2000000000000 : ℝ) ≤
      (-(3668454396237089531377 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (960267200679 / 2000000000000 : ℝ) = (960267200679 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (960267200679 / 500000000000 : ℝ) ≤
            (3263017406762910468623 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (215264327053751 / 312500000000000 : ℝ) ≤ Real.sqrt (949017200679 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (949017200679 / 2000000000000 : ℝ) ≤ (1377691693144007 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (949017200679 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau674 :
    Real.arctan (6888458465720035 / 22142934572579644 : ℝ) ≤
      (754000828193542139837 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau673 :
    Real.arctan (1377691693144007 / 2000000000000000 : ℝ) ≤
      (2 * (754000828193542139837 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3035733643144911 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1377691693144007 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1377691693144007 / 2000000000000000 : ℝ) /
                (1 + (3035733643144911 / 2500000000000000 : ℝ)) =
              (6888458465720035 / 22142934572579644 : ℝ)
            by
        norm_num];
        exact hau674)
  have hat1 :
    (Real.pi / 2 - (2 * (754000828193542139837 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1377691693144007 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1377691693144007 : ℝ) =
              (1377691693144007 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau673)
  have hz1 :
    (2000000000000000 / 1377691693144007 : ℝ) ≤
      1 / Real.sqrt (949017200679 / 2000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1377691693144007 : ℝ) = 1 / (1377691693144007 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (23437500000000 / 215264327053751 : ℝ) ≤
      (54225289558276524857 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (949017200679 / 2000000000000 : ℝ) ≤
      (23437500000000 / 215264327053751 : ℝ) := by
    rw [show
        (23437500000000 / 215264327053751 : ℝ) =
          (3 / 40) / (215264327053751 / 312500000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (754000828193542139837 / 2500000000000000000000 : ℝ))) -
        6 * (54225289558276524857 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (949017200679 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (949017200679 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((215264327053751 / 312500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (754000828193542139837 / 2500000000000000000000 : ℝ))) -
          6 * (54225289558276524857 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (949017200679 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (949017200679 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (949017200679 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_452 :
    ((7784450170672652891 / 20000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7309364856967499426647 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((862258027847523 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ))) -
              6 * (270751843572750147929 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (59479112527 / 125000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (59479112527 / 125000000000 : ℝ)) =
      Real.log (184479112527 / 125000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((59479112527 / 125000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (60182237527 / 125000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (7784450170672652891 / 20000000000000000000 : ℝ) ≤
      Real.log (184479112527 / 125000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (60182237527 / 125000000000 : ℝ) ≤
      (-(7309364856967499426647 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (60182237527 / 125000000000 : ℝ) = (60182237527 / 31250000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (60182237527 / 31250000000 : ℝ) ≤
            (6553578749032500573353 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (862258027847523 / 1250000000000000 : ℝ) ≤ Real.sqrt (59479112527 / 125000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (59479112527 / 125000000000 : ℝ) ≤ (6898064222780187 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (59479112527 / 125000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau676 :
    Real.arctan (6898064222780187 / 22148386313482132 : ℝ) ≤
      (3019259125263958673499 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau675 :
    Real.arctan (6898064222780187 / 10000000000000000 : ℝ) ≤
      (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3037096578370533 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (6898064222780187 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6898064222780187 / 10000000000000000 : ℝ) /
                (1 + (3037096578370533 / 2500000000000000 : ℝ)) =
              (6898064222780187 / 22148386313482132 : ℝ)
            by
        norm_num];
        exact hau676)
  have hat1 :
    (Real.pi / 2 - (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6898064222780187 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6898064222780187 : ℝ) =
              (6898064222780187 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau675)
  have hz1 :
    (10000000000000000 / 6898064222780187 : ℝ) ≤ 1 / Real.sqrt (59479112527 / 125000000000 : ℝ) :=
  by
    rw [show
        (10000000000000000 / 6898064222780187 : ℝ) =
          1 / (6898064222780187 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 287419342615841 : ℝ) ≤
      (270751843572750147929 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (59479112527 / 125000000000 : ℝ) ≤
      (31250000000000 / 287419342615841 : ℝ) := by
    rw [show
        (31250000000000 / 287419342615841 : ℝ) =
          (3 / 40) / (862258027847523 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ))) -
        6 * (270751843572750147929 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (59479112527 / 125000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (59479112527 / 125000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((862258027847523 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ))) -
          6 * (270751843572750147929 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (59479112527 / 125000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (59479112527 / 125000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (59479112527 / 125000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_453 :
    ((780238859810106012883 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7281896579953576581699 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1726914155532383 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (604501498818222252083 / 2000000000000000000000 : ℝ))) -
              6 * (216303030256213961533 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (190862880037 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (190862880037 / 400000000000 : ℝ)) =
      Real.log (590862880037 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((190862880037 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (193112880037 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (780238859810106012883 / 2000000000000000000000 : ℝ) ≤
      Real.log (590862880037 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (193112880037 / 400000000000 : ℝ) ≤
      (-(7281896579953576581699 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (193112880037 / 400000000000 : ℝ) = (193112880037 / 100000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (193112880037 / 100000000000 : ℝ) ≤
            (6581047026046423418301 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1726914155532383 / 2500000000000000 : ℝ) ≤ Real.sqrt (190862880037 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (190862880037 / 400000000000 : ℝ) ≤ (1381531324425907 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (190862880037 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau678 :
    Real.arctan (6907656622129535 / 22153835608944609 : ℝ) ≤
      (604501498818222252083 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau677 :
    Real.arctan (1381531324425907 / 2000000000000000 : ℝ) ≤
      (2 * (604501498818222252083 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12153835608944609 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1381531324425907 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1381531324425907 / 2000000000000000 : ℝ) /
                (1 + (12153835608944609 / 10000000000000000 : ℝ)) =
              (6907656622129535 / 22153835608944609 : ℝ)
            by
        norm_num];
        exact hau678)
  have hat1 :
    (Real.pi / 2 - (2 * (604501498818222252083 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1381531324425907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1381531324425907 : ℝ) =
              (1381531324425907 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau677)
  have hz1 :
    (2000000000000000 / 1381531324425907 : ℝ) ≤ 1 / Real.sqrt (190862880037 / 400000000000 : ℝ) :=
  by
    rw [show
        (2000000000000000 / 1381531324425907 : ℝ) = 1 / (1381531324425907 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1726914155532383 : ℝ) ≤
      (216303030256213961533 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (190862880037 / 400000000000 : ℝ) ≤
      (187500000000000 / 1726914155532383 : ℝ) := by
    rw [show
        (187500000000000 / 1726914155532383 : ℝ) =
          (3 / 40) / (1726914155532383 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (604501498818222252083 / 2000000000000000000000 : ℝ))) -
        6 * (216303030256213961533 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (190862880037 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (190862880037 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1726914155532383 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (604501498818222252083 / 2000000000000000000000 : ℝ))) -
          6 * (216303030256213961533 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (190862880037 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (190862880037 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (190862880037 / 400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_454 :
    ((782031095058741953577 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1813625886732192964727 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6917235719339047 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ))) -
              6 * (33750908736900517841 / 312500000000000000000 : ℝ)))) ≤
      Vfield (478481499969 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (478481499969 / 1000000000000 : ℝ)) =
      Real.log (1478481499969 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((478481499969 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (484106499969 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (782031095058741953577 / 2000000000000000000000 : ℝ) ≤
      Real.log (1478481499969 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (484106499969 / 1000000000000 : ℝ) ≤
      (-(1813625886732192964727 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (484106499969 / 1000000000000 : ℝ) = (484106499969 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (484106499969 / 250000000000 : ℝ) ≤
            (1652110014767807035273 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6917235719339047 / 10000000000000000 : ℝ) ≤ Real.sqrt (478481499969 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (478481499969 / 1000000000000 : ℝ) ≤ (138344714386781 / 200000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (478481499969 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau680 :
    Real.arctan (988176531334150 / 3165611780322131 : ℝ) ≤
      (3025748451398115421169 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau679 :
    Real.arctan (138344714386781 / 200000000000000 : ℝ) ≤
      (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12159282462254917 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (138344714386781 / 200000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (138344714386781 / 200000000000000 : ℝ) /
                (1 + (12159282462254917 / 10000000000000000 : ℝ)) =
              (988176531334150 / 3165611780322131 : ℝ)
            by
        norm_num];
        exact hau680)
  have hat1 :
    (Real.pi / 2 - (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (200000000000000 / 138344714386781 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 138344714386781 : ℝ) =
              (138344714386781 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau679)
  have hz1 :
    (200000000000000 / 138344714386781 : ℝ) ≤ 1 / Real.sqrt (478481499969 / 1000000000000 : ℝ) := by
    rw [show (200000000000000 / 138344714386781 : ℝ) = 1 / (138344714386781 / 200000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6917235719339047 : ℝ) ≤
      (33750908736900517841 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (478481499969 / 1000000000000 : ℝ) ≤
      (750000000000000 / 6917235719339047 : ℝ) := by
    rw [show
        (750000000000000 / 6917235719339047 : ℝ) =
          (3 / 40) / (6917235719339047 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ))) -
        6 * (33750908736900517841 / 312500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (478481499969 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (478481499969 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6917235719339047 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ))) -
          6 * (33750908736900517841 / 312500000000000000000 : ℝ))) ≤
      Real.sqrt (478481499969 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (478481499969 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (478481499969 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_455 :
    ((3919108628458009307323 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(451699084174156310643 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6926801569595449 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (757245507277809449937 / 2500000000000000000000 : ℝ))) -
              6 * (269637279260881504219 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (959611599691 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (959611599691 / 2000000000000 : ℝ)) =
      Real.log (2959611599691 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((959611599691 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (970861599691 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3919108628458009307323 / 10000000000000000000000 : ℝ) ≤
      Real.log (2959611599691 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (970861599691 / 2000000000000 : ℝ) ≤
      (-(451699084174156310643 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (970861599691 / 2000000000000 : ℝ) = (970861599691 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (970861599691 / 500000000000 : ℝ) ≤
            (414734891200843689357 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6926801569595449 / 10000000000000000 : ℝ) ≤ Real.sqrt (959611599691 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (959611599691 / 2000000000000 : ℝ) ≤ (1731700392398863 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (959611599691 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau682 :
    Real.arctan (1731700392398863 / 5541181719173383 : ℝ) ≤
      (757245507277809449937 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau681 :
    Real.arctan (1731700392398863 / 2500000000000000 : ℝ) ≤
      (2 * (757245507277809449937 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3041181719173383 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1731700392398863 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1731700392398863 / 2500000000000000 : ℝ) /
                (1 + (3041181719173383 / 2500000000000000 : ℝ)) =
              (1731700392398863 / 5541181719173383 : ℝ)
            by
        norm_num];
        exact hau682)
  have hat1 :
    (Real.pi / 2 - (2 * (757245507277809449937 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1731700392398863 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1731700392398863 : ℝ) =
              (1731700392398863 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau681)
  have hz1 :
    (2500000000000000 / 1731700392398863 : ℝ) ≤
      1 / Real.sqrt (959611599691 / 2000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1731700392398863 : ℝ) = 1 / (1731700392398863 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6926801569595449 : ℝ) ≤
      (269637279260881504219 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (959611599691 / 2000000000000 : ℝ) ≤
      (750000000000000 / 6926801569595449 : ℝ) := by
    rw [show
        (750000000000000 / 6926801569595449 : ℝ) =
          (3 / 40) / (6926801569595449 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (757245507277809449937 / 2500000000000000000000 : ℝ))) -
        6 * (269637279260881504219 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (959611599691 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (959611599691 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6926801569595449 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (757245507277809449937 / 2500000000000000000000 : ℝ))) -
          6 * (269637279260881504219 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (959611599691 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (959611599691 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (959611599691 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_456 :
    ((245503360806059405313 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7199941571780214482551 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1734088556926231 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (606441651788510147911 / 2000000000000000000000 : ℝ))) -
              6 * (538537610962834018837 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (240565049861 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (240565049861 / 500000000000 : ℝ)) =
      Real.log (740565049861 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((240565049861 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (243377549861 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (245503360806059405313 / 625000000000000000000 : ℝ) ≤
      Real.log (740565049861 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (243377549861 / 500000000000 : ℝ) ≤
      (-(7199941571780214482551 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (243377549861 / 500000000000 : ℝ) = (243377549861 / 125000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (243377549861 / 125000000000 : ℝ) ≤
            (6663002034219785517449 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1734088556926231 / 2500000000000000 : ℝ) ≤ Real.sqrt (240565049861 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (240565049861 / 500000000000 : ℝ) ≤ (6936354227704927 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (240565049861 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau684 :
    Real.arctan (6936354227704927 / 22170168855533598 : ℝ) ≤
      (606441651788510147911 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau683 :
    Real.arctan (6936354227704927 / 10000000000000000 : ℝ) ≤
      (2 * (606441651788510147911 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6085084427766799 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6936354227704927 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6936354227704927 / 10000000000000000 : ℝ) /
                (1 + (6085084427766799 / 5000000000000000 : ℝ)) =
              (6936354227704927 / 22170168855533598 : ℝ)
            by
        norm_num];
        exact hau684)
  have hat1 :
    (Real.pi / 2 - (2 * (606441651788510147911 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6936354227704927 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6936354227704927 : ℝ) =
              (6936354227704927 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau683)
  have hz1 :
    (10000000000000000 / 6936354227704927 : ℝ) ≤
      1 / Real.sqrt (240565049861 / 500000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6936354227704927 : ℝ) =
          1 / (6936354227704927 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1734088556926231 : ℝ) ≤
      (538537610962834018837 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (240565049861 / 500000000000 : ℝ) ≤
      (187500000000000 / 1734088556926231 : ℝ) := by
    rw [show
        (187500000000000 / 1734088556926231 : ℝ) =
          (3 / 40) / (1734088556926231 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (606441651788510147911 / 2000000000000000000000 : ℝ))) -
        6 * (538537610962834018837 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (240565049861 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (240565049861 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1734088556926231 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (606441651788510147911 / 2000000000000000000000 : ℝ))) -
          6 * (538537610962834018837 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (240565049861 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (240565049861 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (240565049861 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
