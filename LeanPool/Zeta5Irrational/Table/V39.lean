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

/-! # V39: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_469 :
    ((841431502833399730677 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6373789591157519530799 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((904028563312041 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1565355854444793571363 / 5000000000000000000000 : ℝ))) -
              6 * (258332775384579108939 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (16737641334457 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (16737641334457 / 32000000000000 : ℝ)) =
      Real.log (48737641334457 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((16737641334457 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (16917641334457 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (841431502833399730677 / 2000000000000000000000 : ℝ) ≤
      Real.log (48737641334457 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (16917641334457 / 32000000000000 : ℝ) ≤
      (-(6373789591157519530799 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16917641334457 / 32000000000000 : ℝ) = (16917641334457 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16917641334457 / 16000000000000 : ℝ) ≤
            (557682211842480469201 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (904028563312041 / 1250000000000000 : ℝ) ≤ Real.sqrt (16737641334457 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (16737641334457 / 32000000000000 : ℝ) ≤
      (7232228506496331 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (16737641334457 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau710 :
    Real.arctan (556325269730487 / 1718553571059557 : ℝ) ≤
      (1565355854444793571363 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau709 :
    Real.arctan (7232228506496331 / 10000000000000000 : ℝ) ≤
      (2 * (1565355854444793571363 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12341196423774241 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7232228506496331 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7232228506496331 / 10000000000000000 : ℝ) /
                (1 + (12341196423774241 / 10000000000000000 : ℝ)) =
              (556325269730487 / 1718553571059557 : ℝ)
            by
        norm_num];
        exact hau710)
  have hat1 :
    (Real.pi / 2 - (2 * (1565355854444793571363 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7232228506496331 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7232228506496331 : ℝ) =
              (7232228506496331 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau709)
  have hz1 :
    (10000000000000000 / 7232228506496331 : ℝ) ≤
      1 / Real.sqrt (16737641334457 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7232228506496331 : ℝ) =
          1 / (7232228506496331 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 301342854437347 : ℝ) ≤
      (258332775384579108939 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (16737641334457 / 32000000000000 : ℝ) ≤
      (31250000000000 / 301342854437347 : ℝ) := by
    rw [show
        (31250000000000 / 301342854437347 : ℝ) =
          (3 / 40) / (904028563312041 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1565355854444793571363 / 5000000000000000000000 : ℝ))) -
        6 * (258332775384579108939 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (16737641334457 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (16737641334457 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((904028563312041 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1565355854444793571363 / 5000000000000000000000 : ℝ))) -
          6 * (258332775384579108939 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (16737641334457 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (16737641334457 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (16737641334457 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_470 :
    ((1053837440410898379117 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6350206894233353416501 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7240853017660129 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3133541876096710658859 / 10000000000000000000000 : ℝ))) -
              6 * (1032109037888209828613 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (33555169550949 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (33555169550949 / 64000000000000 : ℝ)) =
      Real.log (97555169550949 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((33555169550949 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (33915169550949 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1053837440410898379117 / 2500000000000000000000 : ℝ) ≤
      Real.log (97555169550949 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (33915169550949 / 64000000000000 : ℝ) ≤
      (-(6350206894233353416501 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (33915169550949 / 64000000000000 : ℝ) = (33915169550949 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (33915169550949 / 32000000000000 : ℝ) ≤
            (581264908766646583499 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7240853017660129 / 10000000000000000 : ℝ) ≤
      Real.sqrt (33555169550949 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (33555169550949 / 64000000000000 : ℝ) ≤ (1810213254415033 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (33555169550949 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau712 :
    Real.arctan (7240853017660132 / 22346252565995797 : ℝ) ≤
      (3133541876096710658859 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau711 :
    Real.arctan (1810213254415033 / 2500000000000000 : ℝ) ≤
      (2 * (3133541876096710658859 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12346252565995797 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1810213254415033 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1810213254415033 / 2500000000000000 : ℝ) /
                (1 + (12346252565995797 / 10000000000000000 : ℝ)) =
              (7240853017660132 / 22346252565995797 : ℝ)
            by
        norm_num];
        exact hau712)
  have hat1 :
    (Real.pi / 2 - (2 * (3133541876096710658859 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1810213254415033 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1810213254415033 : ℝ) =
              (1810213254415033 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau711)
  have hz1 :
    (2500000000000000 / 1810213254415033 : ℝ) ≤
      1 / Real.sqrt (33555169550949 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1810213254415033 : ℝ) = 1 / (1810213254415033 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7240853017660129 : ℝ) ≤
      (1032109037888209828613 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (33555169550949 / 64000000000000 : ℝ) ≤
      (750000000000000 / 7240853017660129 : ℝ) := by
    rw [show
        (750000000000000 / 7240853017660129 : ℝ) =
          (3 / 40) / (7240853017660129 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3133541876096710658859 / 10000000000000000000000 : ℝ))) -
        6 * (1032109037888209828613 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (33555169550949 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (33555169550949 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7240853017660129 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3133541876096710658859 / 10000000000000000000000 : ℝ))) -
          6 * (1032109037888209828613 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (33555169550949 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (33555169550949 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (33555169550949 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_471 :
    ((422353530332149810381 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6326679680849111885173 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3624733634232227 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (784091590609151552069 / 2500000000000000000000 : ℝ))) -
              6 * (1030891299853228078583 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4204382054123 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4204382054123 / 8000000000000 : ℝ)) =
      Real.log (12204382054123 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4204382054123 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4249382054123 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (422353530332149810381 / 1000000000000000000000 : ℝ) ≤
      Real.log (12204382054123 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4249382054123 / 8000000000000 : ℝ) ≤
      (-(6326679680849111885173 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4249382054123 / 8000000000000 : ℝ) = (4249382054123 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4249382054123 / 4000000000000 : ℝ) ≤
            (604792122150888114827 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3624733634232227 / 5000000000000000 : ℝ) ≤ Real.sqrt (4204382054123 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4204382054123 / 8000000000000 : ℝ) ≤ (7249467268464457 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4204382054123 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau714 :
    Real.arctan (7249467268464457 / 22351306638430506 : ℝ) ≤
      (784091590609151552069 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau713 :
    Real.arctan (7249467268464457 / 10000000000000000 : ℝ) ≤
      (2 * (784091590609151552069 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6175653319215253 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7249467268464457 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7249467268464457 / 10000000000000000 : ℝ) /
                (1 + (6175653319215253 / 5000000000000000 : ℝ)) =
              (7249467268464457 / 22351306638430506 : ℝ)
            by
        norm_num];
        exact hau714)
  have hat1 :
    (Real.pi / 2 - (2 * (784091590609151552069 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7249467268464457 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7249467268464457 : ℝ) =
              (7249467268464457 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau713)
  have hz1 :
    (10000000000000000 / 7249467268464457 : ℝ) ≤
      1 / Real.sqrt (4204382054123 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7249467268464457 : ℝ) =
          1 / (7249467268464457 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3624733634232227 : ℝ) ≤
      (1030891299853228078583 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4204382054123 / 8000000000000 : ℝ) ≤
      (375000000000000 / 3624733634232227 : ℝ) := by
    rw [show
        (375000000000000 / 3624733634232227 : ℝ) =
          (3 / 40) / (3624733634232227 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (784091590609151552069 / 2500000000000000000000 : ℝ))) -
        6 * (1030891299853228078583 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4204382054123 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4204382054123 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3624733634232227 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (784091590609151552069 / 2500000000000000000000 : ℝ))) -
          6 * (1030891299853228078583 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4204382054123 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4204382054123 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4204382054123 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_472 :
    ((846342830033970747269 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(393950480658920792153 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3629035647720933 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3139185189170562755643 / 10000000000000000000000 : ℝ))) -
              6 * (1029677861974945545847 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (33714943315019 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (33714943315019 / 64000000000000 : ℝ)) =
      Real.log (97714943315019 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((33714943315019 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (34074943315019 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (846342830033970747269 / 2000000000000000000000 : ℝ) ≤
      Real.log (97714943315019 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (34074943315019 / 64000000000000 : ℝ) ≤
      (-(393950480658920792153 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34074943315019 / 64000000000000 : ℝ) = (34074943315019 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34074943315019 / 32000000000000 : ℝ) ≤
            (39266507028579207847 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3629035647720933 / 5000000000000000 : ℝ) ≤ Real.sqrt (33714943315019 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (33714943315019 / 64000000000000 : ℝ) ≤
      (7258071295441869 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (33714943315019 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau716 :
    Real.arctan (7258071295441869 / 22356358643618158 : ℝ) ≤
      (3139185189170562755643 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau715 :
    Real.arctan (7258071295441869 / 10000000000000000 : ℝ) ≤
      (2 * (3139185189170562755643 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6178179321809079 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7258071295441869 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7258071295441869 / 10000000000000000 : ℝ) /
                (1 + (6178179321809079 / 5000000000000000 : ℝ)) =
              (7258071295441869 / 22356358643618158 : ℝ)
            by
        norm_num];
        exact hau716)
  have hat1 :
    (Real.pi / 2 - (2 * (3139185189170562755643 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7258071295441869 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7258071295441869 : ℝ) =
              (7258071295441869 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau715)
  have hz1 :
    (10000000000000000 / 7258071295441869 : ℝ) ≤
      1 / Real.sqrt (33714943315019 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7258071295441869 : ℝ) =
          1 / (7258071295441869 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1209678549240311 : ℝ) ≤
      (1029677861974945545847 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (33714943315019 / 64000000000000 : ℝ) ≤
      (125000000000000 / 1209678549240311 : ℝ) := by
    rw [show
        (125000000000000 / 1209678549240311 : ℝ) =
          (3 / 40) / (3629035647720933 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3139185189170562755643 / 10000000000000000000000 : ℝ))) -
        6 * (1029677861974945545847 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (33714943315019 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (33714943315019 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3629035647720933 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3139185189170562755643 / 10000000000000000000000 : ℝ))) -
          6 * (1029677861974945545847 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (33714943315019 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (33714943315019 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (33714943315019 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_473 :
    ((33919090505047273979 / 80000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6279790664681930096523 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7266665134908643 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1570999188718471372011 / 5000000000000000000000 : ℝ))) -
              6 * (102846869900421664989 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (16897415098527 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (16897415098527 / 32000000000000 : ℝ)) =
      Real.log (48897415098527 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((16897415098527 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (17077415098527 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (33919090505047273979 / 80000000000000000000 : ℝ) ≤
      Real.log (48897415098527 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (17077415098527 / 32000000000000 : ℝ) ≤
      (-(6279790664681930096523 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17077415098527 / 32000000000000 : ℝ) = (17077415098527 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17077415098527 / 16000000000000 : ℝ) ≤
            (651681138318069903477 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7266665134908643 / 10000000000000000 : ℝ) ≤
      Real.sqrt (16897415098527 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (16897415098527 / 32000000000000 : ℝ) ≤ (3633332567454323 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (16897415098527 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau718 :
    Real.arctan (3633332567454323 / 11180704292046677 : ℝ) ≤
      (1570999188718471372011 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau717 :
    Real.arctan (3633332567454323 / 5000000000000000 : ℝ) ≤
      (2 * (1570999188718471372011 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6180704292046677 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3633332567454323 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3633332567454323 / 5000000000000000 : ℝ) /
                (1 + (6180704292046677 / 5000000000000000 : ℝ)) =
              (3633332567454323 / 11180704292046677 : ℝ)
            by
        norm_num];
        exact hau718)
  have hat1 :
    (Real.pi / 2 - (2 * (1570999188718471372011 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3633332567454323 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3633332567454323 : ℝ) =
              (3633332567454323 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau717)
  have hz1 :
    (5000000000000000 / 3633332567454323 : ℝ) ≤
      1 / Real.sqrt (16897415098527 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3633332567454323 : ℝ) = 1 / (3633332567454323 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7266665134908643 : ℝ) ≤
      (102846869900421664989 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (16897415098527 / 32000000000000 : ℝ) ≤
      (750000000000000 / 7266665134908643 : ℝ) := by
    rw [show
        (750000000000000 / 7266665134908643 : ℝ) =
          (3 / 40) / (7266665134908643 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1570999188718471372011 / 5000000000000000000000 : ℝ))) -
        6 * (102846869900421664989 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (16897415098527 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (16897415098527 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7266665134908643 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1570999188718471372011 / 5000000000000000000000 : ℝ))) -
          6 * (102846869900421664989 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (16897415098527 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (16897415098527 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (16897415098527 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_474 :
    ((531006475390013602341 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(782053543305886984727 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((291009952918663 / 400000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3144805948252172401271 / 10000000000000000000000 : ℝ))) -
              6 * (1027263785898967908693 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (33874717079089 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (33874717079089 / 64000000000000 : ℝ)) =
      Real.log (97874717079089 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((33874717079089 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (34234717079089 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (531006475390013602341 / 1250000000000000000000 : ℝ) ≤
      Real.log (97874717079089 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (34234717079089 / 64000000000000 : ℝ) ≤
      (-(782053543305886984727 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34234717079089 / 64000000000000 : ℝ) = (34234717079089 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34234717079089 / 32000000000000 : ℝ) ≤
            (84380432069113015273 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (291009952918663 / 400000000000000 : ℝ) ≤ Real.sqrt (33874717079089 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (33874717079089 / 64000000000000 : ℝ) ≤ (3637624411483289 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (33874717079089 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau720 :
    Real.arctan (3637624411483289 / 11183228231192759 : ℝ) ≤
      (3144805948252172401271 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau719 :
    Real.arctan (3637624411483289 / 5000000000000000 : ℝ) ≤
      (2 * (3144805948252172401271 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6183228231192759 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3637624411483289 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3637624411483289 / 5000000000000000 : ℝ) /
                (1 + (6183228231192759 / 5000000000000000 : ℝ)) =
              (3637624411483289 / 11183228231192759 : ℝ)
            by
        norm_num];
        exact hau720)
  have hat1 :
    (Real.pi / 2 - (2 * (3144805948252172401271 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3637624411483289 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3637624411483289 : ℝ) =
              (3637624411483289 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau719)
  have hz1 :
    (5000000000000000 / 3637624411483289 : ℝ) ≤
      1 / Real.sqrt (33874717079089 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3637624411483289 : ℝ) = 1 / (3637624411483289 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (30000000000000 / 291009952918663 : ℝ) ≤
      (1027263785898967908693 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (33874717079089 / 64000000000000 : ℝ) ≤
      (30000000000000 / 291009952918663 : ℝ) := by
    rw [show
        (30000000000000 / 291009952918663 : ℝ) =
          (3 / 40) / (291009952918663 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3144805948252172401271 / 10000000000000000000000 : ℝ))) -
        6 * (1027263785898967908693 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (33874717079089 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (33874717079089 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((291009952918663 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3144805948252172401271 / 10000000000000000000000 : ℝ))) -
          6 * (1027263785898967908693 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (33874717079089 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (33874717079089 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (33874717079089 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_475 :
    ((425621063102617945859 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1246624096162879854307 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((910477799438091 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (629521584502343043317 / 2000000000000000000000 : ℝ))) -
              6 * (513031548911010165729 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (8488650990281 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8488650990281 / 16000000000000 : ℝ)) =
      Real.log (24488650990281 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8488650990281 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8578650990281 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (425621063102617945859 / 1000000000000000000000 : ℝ) ≤
      Real.log (24488650990281 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8578650990281 / 16000000000000 : ℝ) ≤
      (-(1246624096162879854307 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8578650990281 / 16000000000000 : ℝ) = (8578650990281 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8578650990281 / 8000000000000 : ℝ) ≤
            (139670264437120145693 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (910477799438091 / 1250000000000000 : ℝ) ≤ Real.sqrt (8488650990281 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8488650990281 / 16000000000000 : ℝ) ≤ (7283822395504731 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8488650990281 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau722 :
    Real.arctan (7283822395504731 / 22371502281018916 : ℝ) ≤
      (629521584502343043317 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau721 :
    Real.arctan (7283822395504731 / 10000000000000000 : ℝ) ≤
      (2 * (629521584502343043317 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3092875570254729 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (7283822395504731 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7283822395504731 / 10000000000000000 : ℝ) /
                (1 + (3092875570254729 / 2500000000000000 : ℝ)) =
              (7283822395504731 / 22371502281018916 : ℝ)
            by
        norm_num];
        exact hau722)
  have hat1 :
    (Real.pi / 2 - (2 * (629521584502343043317 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7283822395504731 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7283822395504731 : ℝ) =
              (7283822395504731 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau721)
  have hz1 :
    (10000000000000000 / 7283822395504731 : ℝ) ≤
      1 / Real.sqrt (8488650990281 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7283822395504731 : ℝ) =
          1 / (7283822395504731 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 303492599812697 : ℝ) ≤
      (513031548911010165729 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8488650990281 / 16000000000000 : ℝ) ≤
      (31250000000000 / 303492599812697 : ℝ) := by
    rw [show
        (31250000000000 / 303492599812697 : ℝ) =
          (3 / 40) / (910477799438091 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (629521584502343043317 / 2000000000000000000000 : ℝ))) -
        6 * (513031548911010165729 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8488650990281 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8488650990281 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((910477799438091 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (629521584502343043317 / 2000000000000000000000 : ℝ))) -
          6 * (513031548911010165729 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (8488650990281 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8488650990281 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8488650990281 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_476 :
    ((4264362807711218122773 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(776233351817385457859 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3646192944100597 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (157520216049551920661 / 500000000000000000000 : ℝ))) -
              6 * (512433305069469542579 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (34034490843159 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (34034490843159 / 64000000000000 : ℝ)) =
      Real.log (98034490843159 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((34034490843159 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (34394490843159 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4264362807711218122773 / 10000000000000000000000 : ℝ) ≤
      Real.log (98034490843159 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (34394490843159 / 64000000000000 : ℝ) ≤
      (-(776233351817385457859 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34394490843159 / 64000000000000 : ℝ) = (34394490843159 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34394490843159 / 32000000000000 : ℝ) ≤
            (90200623557614542141 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3646192944100597 / 5000000000000000 : ℝ) ≤ Real.sqrt (34034490843159 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (34034490843159 / 64000000000000 : ℝ) ≤
      (7292385888201197 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (34034490843159 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau724 :
    Real.arctan (7292385888201197 / 22376546042512666 : ℝ) ≤
      (157520216049551920661 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau723 :
    Real.arctan (7292385888201197 / 10000000000000000 : ℝ) ≤
      (2 * (157520216049551920661 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6188273021256333 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7292385888201197 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7292385888201197 / 10000000000000000 : ℝ) /
                (1 + (6188273021256333 / 5000000000000000 : ℝ)) =
              (7292385888201197 / 22376546042512666 : ℝ)
            by
        norm_num];
        exact hau724)
  have hat1 :
    (Real.pi / 2 - (2 * (157520216049551920661 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7292385888201197 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7292385888201197 : ℝ) =
              (7292385888201197 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau723)
  have hz1 :
    (10000000000000000 / 7292385888201197 : ℝ) ≤
      1 / Real.sqrt (34034490843159 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7292385888201197 : ℝ) =
          1 / (7292385888201197 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3646192944100597 : ℝ) ≤
      (512433305069469542579 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (34034490843159 / 64000000000000 : ℝ) ≤
      (375000000000000 / 3646192944100597 : ℝ) := by
    rw [show
        (375000000000000 / 3646192944100597 : ℝ) =
          (3 / 40) / (3646192944100597 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (157520216049551920661 / 500000000000000000000 : ℝ))) -
        6 * (512433305069469542579 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (34034490843159 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (34034490843159 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3646192944100597 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (157520216049551920661 / 500000000000000000000 : ℝ))) -
          6 * (512433305069469542579 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (34034490843159 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (34034490843159 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (34034490843159 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_477 :
    ((2136254172005389240579 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6186667096138956931663 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7300939336524829 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3153195164346571015303 / 10000000000000000000000 : ℝ))) -
              6 * (1023674298415909778301 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (17057188862597 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (17057188862597 / 32000000000000 : ℝ)) =
      Real.log (49057188862597 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((17057188862597 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (17237188862597 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2136254172005389240579 / 5000000000000000000000 : ℝ) ≤
      Real.log (49057188862597 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (17237188862597 / 32000000000000 : ℝ) ≤
      (-(6186667096138956931663 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17237188862597 / 32000000000000 : ℝ) = (17237188862597 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17237188862597 / 16000000000000 : ℝ) ≤
            (744804706861043068337 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7300939336524829 / 10000000000000000 : ℝ) ≤
      Real.sqrt (17057188862597 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (17057188862597 / 32000000000000 : ℝ) ≤ (228154354266401 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (17057188862597 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau726 :
    Real.arctan (1825234834131208 / 5595396937345189 : ℝ) ≤
      (3153195164346571015303 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau725 :
    Real.arctan (228154354266401 / 312500000000000 : ℝ) ≤
      (2 * (3153195164346571015303 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3095396937345189 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (228154354266401 / 312500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (228154354266401 / 312500000000000 : ℝ) /
                (1 + (3095396937345189 / 2500000000000000 : ℝ)) =
              (1825234834131208 / 5595396937345189 : ℝ)
            by
        norm_num];
        exact hau726)
  have hat1 :
    (Real.pi / 2 - (2 * (3153195164346571015303 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (312500000000000 / 228154354266401 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 228154354266401 : ℝ) =
              (228154354266401 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau725)
  have hz1 :
    (312500000000000 / 228154354266401 : ℝ) ≤
      1 / Real.sqrt (17057188862597 / 32000000000000 : ℝ) := by
    rw [show (312500000000000 / 228154354266401 : ℝ) = 1 / (228154354266401 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7300939336524829 : ℝ) ≤
      (1023674298415909778301 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (17057188862597 / 32000000000000 : ℝ) ≤
      (750000000000000 / 7300939336524829 : ℝ) := by
    rw [show
        (750000000000000 / 7300939336524829 : ℝ) =
          (3 / 40) / (7300939336524829 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3153195164346571015303 / 10000000000000000000000 : ℝ))) -
        6 * (1023674298415909778301 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (17057188862597 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (17057188862597 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7300939336524829 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3153195164346571015303 / 10000000000000000000000 : ℝ))) -
          6 * (1023674298415909778301 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (17057188862597 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (17057188862597 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (17057188862597 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_478 :
    ((4280647250733957331043 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(770440134484759110209 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((11421066837089 / 15625000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3155980473116647307711 / 10000000000000000000000 : ℝ))) -
              6 * (127810767302205454203 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (34194264607229 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (34194264607229 / 64000000000000 : ℝ)) =
      Real.log (98194264607229 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((34194264607229 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (34554264607229 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4280647250733957331043 / 10000000000000000000000 : ℝ) ≤
      Real.log (98194264607229 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (34554264607229 / 64000000000000 : ℝ) ≤
      (-(770440134484759110209 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34554264607229 / 64000000000000 : ℝ) = (34554264607229 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34554264607229 / 32000000000000 : ℝ) ≤
            (95993840890240889791 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (11421066837089 / 15625000000000 : ℝ) ≤ Real.sqrt (34194264607229 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (34194264607229 / 64000000000000 : ℝ) ≤
      (7309482775736963 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (34194264607229 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau728 :
    Real.arctan (7309482775736963 / 22386627404132059 : ℝ) ≤
      (3155980473116647307711 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau727 :
    Real.arctan (7309482775736963 / 10000000000000000 : ℝ) ≤
      (2 * (3155980473116647307711 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12386627404132059 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7309482775736963 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7309482775736963 / 10000000000000000 : ℝ) /
                (1 + (12386627404132059 / 10000000000000000 : ℝ)) =
              (7309482775736963 / 22386627404132059 : ℝ)
            by
        norm_num];
        exact hau728)
  have hat1 :
    (Real.pi / 2 - (2 * (3155980473116647307711 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7309482775736963 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7309482775736963 : ℝ) =
              (7309482775736963 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau727)
  have hz1 :
    (10000000000000000 / 7309482775736963 : ℝ) ≤
      1 / Real.sqrt (34194264607229 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7309482775736963 : ℝ) =
          1 / (7309482775736963 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (1171875000000 / 11421066837089 : ℝ) ≤
      (127810767302205454203 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (34194264607229 / 64000000000000 : ℝ) ≤
      (1171875000000 / 11421066837089 : ℝ) := by
    rw [show
        (1171875000000 / 11421066837089 : ℝ) = (3 / 40) / (11421066837089 / 15625000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3155980473116647307711 / 10000000000000000000000 : ℝ))) -
        6 * (127810767302205454203 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (34194264607229 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (34194264607229 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((11421066837089 / 15625000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3155980473116647307711 / 10000000000000000000000 : ℝ))) -
          6 * (127810767302205454203 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (34194264607229 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (34194264607229 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (34194264607229 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_479 :
    ((4284714221375033324851 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6151968124980879444211 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7313750752889049 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (631474211683661753521 / 2000000000000000000000 : ℝ))) -
              6 * (1021893607795543436653 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (68468416096493 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (68468416096493 / 128000000000000 : ℝ)) =
      Real.log (196468416096493 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((68468416096493 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69188416096493 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4284714221375033324851 / 10000000000000000000000 : ℝ) ≤
      Real.log (196468416096493 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69188416096493 / 128000000000000 : ℝ) ≤
      (-(6151968124980879444211 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69188416096493 / 128000000000000 : ℝ) = (69188416096493 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69188416096493 / 64000000000000 : ℝ) ≤
            (779503678019120555789 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7313750752889049 / 10000000000000000 : ℝ) ≤
      Real.sqrt (68468416096493 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (68468416096493 / 128000000000000 : ℝ) ≤
      (1828437688222263 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (68468416096493 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau730 :
    Real.arctan (7313750752889052 / 22389146462746541 : ℝ) ≤
      (631474211683661753521 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau729 :
    Real.arctan (1828437688222263 / 2500000000000000 : ℝ) ≤
      (2 * (631474211683661753521 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12389146462746541 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1828437688222263 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1828437688222263 / 2500000000000000 : ℝ) /
                (1 + (12389146462746541 / 10000000000000000 : ℝ)) =
              (7313750752889052 / 22389146462746541 : ℝ)
            by
        norm_num];
        exact hau730)
  have hat1 :
    (Real.pi / 2 - (2 * (631474211683661753521 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1828437688222263 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1828437688222263 : ℝ) =
              (1828437688222263 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau729)
  have hz1 :
    (2500000000000000 / 1828437688222263 : ℝ) ≤
      1 / Real.sqrt (68468416096493 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1828437688222263 : ℝ) = 1 / (1828437688222263 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2437916917629683 : ℝ) ≤
      (1021893607795543436653 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (68468416096493 / 128000000000000 : ℝ) ≤
      (250000000000000 / 2437916917629683 : ℝ) := by
    rw [show
        (250000000000000 / 2437916917629683 : ℝ) =
          (3 / 40) / (7313750752889049 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (631474211683661753521 / 2000000000000000000000 : ℝ))) -
        6 * (1021893607795543436653 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (68468416096493 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (68468416096493 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7313750752889049 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (631474211683661753521 / 2000000000000000000000 : ℝ))) -
          6 * (1021893607795543436653 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (68468416096493 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (68468416096493 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (68468416096493 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_480 :
    ((4288779538663480659127 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(383776781609412568073 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3659008120446543 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1579380133861223043083 / 5000000000000000000000 : ℝ))) -
              6 * (127662763263163460067 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (2142134468079 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2142134468079 / 4000000000000 : ℝ)) =
      Real.log (6142134468079 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2142134468079 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2164634468079 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4288779538663480659127 / 10000000000000000000000 : ℝ) ≤
      Real.log (6142134468079 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2164634468079 / 4000000000000 : ℝ) ≤
      (-(383776781609412568073 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2164634468079 / 4000000000000 : ℝ) = (2164634468079 / 2000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2164634468079 / 2000000000000 : ℝ) ≤
            (49440206078087431927 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3659008120446543 / 5000000000000000 : ℝ) ≤ Real.sqrt (2142134468079 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2142134468079 / 4000000000000 : ℝ) ≤ (7318016240893089 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2142134468079 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau732 :
    Real.arctan (7318016240893089 / 22391665009270343 : ℝ) ≤
      (1579380133861223043083 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau731 :
    Real.arctan (7318016240893089 / 10000000000000000 : ℝ) ≤
      (2 * (1579380133861223043083 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12391665009270343 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7318016240893089 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7318016240893089 / 10000000000000000 : ℝ) /
                (1 + (12391665009270343 / 10000000000000000 : ℝ)) =
              (7318016240893089 / 22391665009270343 : ℝ)
            by
        norm_num];
        exact hau732)
  have hat1 :
    (Real.pi / 2 - (2 * (1579380133861223043083 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7318016240893089 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7318016240893089 : ℝ) =
              (7318016240893089 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau731)
  have hz1 :
    (10000000000000000 / 7318016240893089 : ℝ) ≤
      1 / Real.sqrt (2142134468079 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7318016240893089 : ℝ) =
          1 / (7318016240893089 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1219669373482181 : ℝ) ≤
      (127662763263163460067 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2142134468079 / 4000000000000 : ℝ) ≤
      (125000000000000 / 1219669373482181 : ℝ) := by
    rw [show
        (125000000000000 / 1219669373482181 : ℝ) =
          (3 / 40) / (3659008120446543 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1579380133861223043083 / 5000000000000000000000 : ℝ))) -
        6 * (127662763263163460067 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2142134468079 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2142134468079 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3659008120446543 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1579380133861223043083 / 5000000000000000000000 : ℝ))) -
          6 * (127662763263163460067 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (2142134468079 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2142134468079 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2142134468079 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
