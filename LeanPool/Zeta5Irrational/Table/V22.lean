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

/-! # V22: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_265 :
    ((501012873635738876091 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7402526123330008104227 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4710601968739139 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2201144530125916720343 / 5000000000000000000000 : ℝ)) -
              6 * (789450375468092547361 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (14201453381049 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14201453381049 / 64000000000000 : ℝ)) =
      Real.log (78201453381049 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14201453381049 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14561453381049 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (501012873635738876091 / 2500000000000000000000 : ℝ) ≤
      Real.log (78201453381049 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14561453381049 / 64000000000000 : ℝ) ≤
      (-(7402526123330008104227 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14561453381049 / 64000000000000 : ℝ) = (14561453381049 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14561453381049 / 8000000000000 : ℝ) ≤
            (2994681581169991895773 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4710601968739139 / 10000000000000000 : ℝ) ≤
      Real.sqrt (14201453381049 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14201453381049 / 64000000000000 : ℝ) ≤ (2355300984369571 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14201453381049 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau327 :
    Real.arctan (2355300984369571 / 5000000000000000 : ℝ) ≤
      (2201144530125916720343 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2201144530125916720343 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2355300984369571 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2355300984369571 : ℝ) =
              (2355300984369571 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau327)
  have hz1 :
    (5000000000000000 / 2355300984369571 : ℝ) ≤
      1 / Real.sqrt (14201453381049 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2355300984369571 : ℝ) = 1 / (2355300984369571 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4710601968739139 : ℝ) ≤
      (789450375468092547361 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (14201453381049 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4710601968739139 : ℝ) := by
    rw [show
        (750000000000000 / 4710601968739139 : ℝ) =
          (3 / 40) / (4710601968739139 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2201144530125916720343 / 5000000000000000000000 : ℝ)) -
        6 * (789450375468092547361 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14201453381049 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14201453381049 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4710601968739139 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2201144530125916720343 / 5000000000000000000000 : ℝ)) -
          6 * (789450375468092547361 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (14201453381049 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14201453381049 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14201453381049 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_266 :
    ((1004206824111706414963 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14781647848946051308547 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4716257371140541 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4406916427345624348069 / 10000000000000000000000 : ℝ)) -
              6 * (39425967473124423959 / 250000000000000000000 : ℝ)))) ≤
      Vfield (1779446687267 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1779446687267 / 8000000000000 : ℝ)) =
      Real.log (9779446687267 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1779446687267 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1824446687267 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1004206824111706414963 / 5000000000000000000000 : ℝ) ≤
      Real.log (9779446687267 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1824446687267 / 8000000000000 : ℝ) ≤
      (-(14781647848946051308547 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1824446687267 / 8000000000000 : ℝ) = (1824446687267 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1824446687267 / 1000000000000 : ℝ) ≤
            (6012767560053948691453 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4716257371140541 / 10000000000000000 : ℝ) ≤ Real.sqrt (1779446687267 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1779446687267 / 8000000000000 : ℝ) ≤ (73691521424071 / 156250000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1779446687267 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau328 :
    Real.arctan (73691521424071 / 156250000000000 : ℝ) ≤
      (4406916427345624348069 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4406916427345624348069 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (156250000000000 / 73691521424071 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (156250000000000 / 73691521424071 : ℝ) =
              (73691521424071 / 156250000000000 : ℝ)
            by
        norm_num];
        exact hau328)
  have hz1 :
    (156250000000000 / 73691521424071 : ℝ) ≤ 1 / Real.sqrt (1779446687267 / 8000000000000 : ℝ) := by
    rw [show (156250000000000 / 73691521424071 : ℝ) = 1 / (73691521424071 / 156250000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4716257371140541 : ℝ) ≤
      (39425967473124423959 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1779446687267 / 8000000000000 : ℝ) ≤
      (750000000000000 / 4716257371140541 : ℝ) := by
    rw [show
        (750000000000000 / 4716257371140541 : ℝ) =
          (3 / 40) / (4716257371140541 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4406916427345624348069 / 10000000000000000000000 : ℝ)) -
        6 * (39425967473124423959 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1779446687267 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1779446687267 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4716257371140541 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4406916427345624348069 / 10000000000000000000000 : ℝ)) -
          6 * (39425967473124423959 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (1779446687267 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1779446687267 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1779446687267 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_267 :
    ((125798368743440768183 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7379149049969101912307 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4721906000100587 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2205768118518581484771 / 5000000000000000000000 : ℝ)) -
              6 * (1575183219723586415793 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (14269693615223 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14269693615223 / 64000000000000 : ℝ)) =
      Real.log (78269693615223 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14269693615223 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14629693615223 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (125798368743440768183 / 625000000000000000000 : ℝ) ≤
      Real.log (78269693615223 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14629693615223 / 64000000000000 : ℝ) ≤
      (-(7379149049969101912307 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14629693615223 / 64000000000000 : ℝ) = (14629693615223 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14629693615223 / 8000000000000 : ℝ) ≤
            (3018058654530898087693 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4721906000100587 / 10000000000000000 : ℝ) ≤
      Real.sqrt (14269693615223 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14269693615223 / 64000000000000 : ℝ) ≤ (472190600010059 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14269693615223 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau329 :
    Real.arctan (472190600010059 / 1000000000000000 : ℝ) ≤
      (2205768118518581484771 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2205768118518581484771 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 472190600010059 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 472190600010059 : ℝ) =
              (472190600010059 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau329)
  have hz1 :
    (1000000000000000 / 472190600010059 : ℝ) ≤
      1 / Real.sqrt (14269693615223 / 64000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 472190600010059 : ℝ) = 1 / (472190600010059 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4721906000100587 : ℝ) ≤
      (1575183219723586415793 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (14269693615223 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4721906000100587 : ℝ) := by
    rw [show
        (750000000000000 / 4721906000100587 : ℝ) =
          (3 / 40) / (4721906000100587 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2205768118518581484771 / 5000000000000000000000 : ℝ)) -
        6 * (1575183219723586415793 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14269693615223 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14269693615223 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4721906000100587 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2205768118518581484771 / 5000000000000000000000 : ℝ)) -
          6 * (1575183219723586415793 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (14269693615223 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14269693615223 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14269693615223 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_268 :
    ((2017132251215798468539 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(92093767156400260889 / 62500000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((945509575979733 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2208074257881297602699 / 5000000000000000000000 : ℝ)) -
              6 * (314666854950398720743 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (1430381373231 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1430381373231 / 6400000000000 : ℝ)) =
      Real.log (7830381373231 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1430381373231 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1466381373231 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2017132251215798468539 / 10000000000000000000000 : ℝ) ≤
      Real.log (7830381373231 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1466381373231 / 6400000000000 : ℝ) ≤
      (-(92093767156400260889 / 62500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1466381373231 / 6400000000000 : ℝ) = (1466381373231 / 800000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1466381373231 / 800000000000 : ℝ) ≤
            (37871329149849739111 / 62500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (945509575979733 / 2000000000000000 : ℝ) ≤ Real.sqrt (1430381373231 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1430381373231 / 6400000000000 : ℝ) ≤ (1181886969974667 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1430381373231 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau330 :
    Real.arctan (1181886969974667 / 2500000000000000 : ℝ) ≤
      (2208074257881297602699 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2208074257881297602699 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1181886969974667 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1181886969974667 : ℝ) =
              (1181886969974667 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau330)
  have hz1 :
    (2500000000000000 / 1181886969974667 : ℝ) ≤
      1 / Real.sqrt (1430381373231 / 6400000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1181886969974667 : ℝ) = 1 / (1181886969974667 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 315169858659911 : ℝ) ≤
      (314666854950398720743 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1430381373231 / 6400000000000 : ℝ) ≤
      (50000000000000 / 315169858659911 : ℝ) := by
    rw [show
        (50000000000000 / 315169858659911 : ℝ) =
          (3 / 40) / (945509575979733 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2208074257881297602699 / 5000000000000000000000 : ℝ)) -
        6 * (314666854950398720743 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1430381373231 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1430381373231 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((945509575979733 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2208074257881297602699 / 5000000000000000000000 : ℝ)) -
          6 * (314666854950398720743 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (1430381373231 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1430381373231 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1430381373231 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_269 :
    ((1010744351920704571427 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3677940382841596508797 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((236659151733473 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2210376644902636965323 / 5000000000000000000000 : ℝ)) -
              6 * (785745912873242323847 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (14337933849397 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14337933849397 / 64000000000000 : ℝ)) =
      Real.log (78337933849397 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14337933849397 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14697933849397 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1010744351920704571427 / 5000000000000000000000 : ℝ) ≤
      Real.log (78337933849397 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14697933849397 / 64000000000000 : ℝ) ≤
      (-(3677940382841596508797 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14697933849397 / 64000000000000 : ℝ) = (14697933849397 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14697933849397 / 8000000000000 : ℝ) ≤
            (1520663469408403491203 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (236659151733473 / 500000000000000 : ℝ) ≤ Real.sqrt (14337933849397 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14337933849397 / 64000000000000 : ℝ) ≤
      (4733183034669463 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14337933849397 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau331 :
    Real.arctan (4733183034669463 / 10000000000000000 : ℝ) ≤
      (2210376644902636965323 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2210376644902636965323 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4733183034669463 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4733183034669463 : ℝ) =
              (4733183034669463 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau331)
  have hz1 :
    (10000000000000000 / 4733183034669463 : ℝ) ≤
      1 / Real.sqrt (14337933849397 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4733183034669463 : ℝ) =
          1 / (4733183034669463 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (37500000000000 / 236659151733473 : ℝ) ≤
      (785745912873242323847 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (14337933849397 / 64000000000000 : ℝ) ≤
      (37500000000000 / 236659151733473 : ℝ) := by
    rw [show
        (37500000000000 / 236659151733473 : ℝ) =
          (3 / 40) / (236659151733473 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2210376644902636965323 / 5000000000000000000000 : ℝ)) -
        6 * (785745912873242323847 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14337933849397 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14337933849397 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((236659151733473 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2210376644902636965323 / 5000000000000000000000 : ℝ)) -
          6 * (785745912873242323847 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (14337933849397 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14337933849397 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14337933849397 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_270 :
    ((506460814856369766769 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7344287103943422644799 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2369405744202079 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4425350585297006953787 / 10000000000000000000000 : ℝ)) -
              6 * (9810348967227032483 / 62500000000000000000 : ℝ)))) ≤
      Vfield (3593013491621 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3593013491621 / 16000000000000 : ℝ)) =
      Real.log (19593013491621 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3593013491621 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3683013491621 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (506460814856369766769 / 2500000000000000000000 : ℝ) ≤
      Real.log (19593013491621 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3683013491621 / 16000000000000 : ℝ) ≤
      (-(7344287103943422644799 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3683013491621 / 16000000000000 : ℝ) = (3683013491621 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3683013491621 / 2000000000000 : ℝ) ≤
            (3052920600556577355201 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2369405744202079 / 5000000000000000 : ℝ) ≤ Real.sqrt (3593013491621 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3593013491621 / 16000000000000 : ℝ) ≤ (4738811488404161 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3593013491621 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau332 :
    Real.arctan (4738811488404161 / 10000000000000000 : ℝ) ≤
      (4425350585297006953787 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4425350585297006953787 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4738811488404161 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4738811488404161 : ℝ) =
              (4738811488404161 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau332)
  have hz1 :
    (10000000000000000 / 4738811488404161 : ℝ) ≤
      1 / Real.sqrt (3593013491621 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4738811488404161 : ℝ) =
          1 / (4738811488404161 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2369405744202079 : ℝ) ≤
      (9810348967227032483 / 62500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3593013491621 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2369405744202079 : ℝ) := by
    rw [show
        (375000000000000 / 2369405744202079 : ℝ) =
          (3 / 40) / (2369405744202079 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4425350585297006953787 / 10000000000000000000000 : ℝ)) -
        6 * (9810348967227032483 / 62500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3593013491621 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3593013491621 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2369405744202079 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4425350585297006953787 / 10000000000000000000000 : ℝ)) -
          6 * (9810348967227032483 / 62500000000000000000 : ℝ))) ≤
      Real.sqrt (3593013491621 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3593013491621 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3593013491621 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_271 :
    ((2030195919619443733491 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14665440525249540781007 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4744433264951639 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4429940428219294879569 / 10000000000000000000000 : ℝ)) -
              6 * (1567826264140476018089 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (14406174083571 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14406174083571 / 64000000000000 : ℝ)) =
      Real.log (78406174083571 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14406174083571 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14766174083571 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2030195919619443733491 / 10000000000000000000000 : ℝ) ≤
      Real.log (78406174083571 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14766174083571 / 64000000000000 : ℝ) ≤
      (-(14665440525249540781007 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14766174083571 / 64000000000000 : ℝ) = (14766174083571 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14766174083571 / 8000000000000 : ℝ) ≤
            (6128974883750459218993 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4744433264951639 / 10000000000000000 : ℝ) ≤
      Real.sqrt (14406174083571 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14406174083571 / 64000000000000 : ℝ) ≤ (2372216632475821 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14406174083571 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau333 :
    Real.arctan (2372216632475821 / 5000000000000000 : ℝ) ≤
      (4429940428219294879569 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4429940428219294879569 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2372216632475821 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2372216632475821 : ℝ) =
              (2372216632475821 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau333)
  have hz1 :
    (5000000000000000 / 2372216632475821 : ℝ) ≤
      1 / Real.sqrt (14406174083571 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2372216632475821 : ℝ) = 1 / (2372216632475821 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4744433264951639 : ℝ) ≤
      (1567826264140476018089 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (14406174083571 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4744433264951639 : ℝ) := by
    rw [show
        (750000000000000 / 4744433264951639 : ℝ) =
          (3 / 40) / (4744433264951639 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4429940428219294879569 / 10000000000000000000000 : ℝ)) -
        6 * (1567826264140476018089 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14406174083571 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14406174083571 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4744433264951639 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4429940428219294879569 / 10000000000000000000000 : ℝ)) -
          6 * (1567826264140476018089 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (14406174083571 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14406174083571 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14406174083571 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_272 :
    ((1017273343036291565619 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(58569440943380077467 / 40000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2375024194009827 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4434522844404553221673 / 10000000000000000000000 : ℝ)) -
              6 * (1566003076564351681379 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7220147100329 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7220147100329 / 32000000000000 : ℝ)) =
      Real.log (39220147100329 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7220147100329 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7400147100329 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1017273343036291565619 / 5000000000000000000000 : ℝ) ≤
      Real.log (39220147100329 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7400147100329 / 32000000000000 : ℝ) ≤
      (-(58569440943380077467 / 40000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7400147100329 / 32000000000000 : ℝ) = (7400147100329 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7400147100329 / 4000000000000 : ℝ) ≤
            (24608220692619922533 / 40000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2375024194009827 / 5000000000000000 : ℝ) ≤ Real.sqrt (7220147100329 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7220147100329 / 32000000000000 : ℝ) ≤ (4750048388019657 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7220147100329 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau334 :
    Real.arctan (4750048388019657 / 10000000000000000 : ℝ) ≤
      (4434522844404553221673 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4434522844404553221673 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4750048388019657 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4750048388019657 : ℝ) =
              (4750048388019657 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau334)
  have hz1 :
    (10000000000000000 / 4750048388019657 : ℝ) ≤
      1 / Real.sqrt (7220147100329 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4750048388019657 : ℝ) =
          1 / (4750048388019657 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 791674731336609 : ℝ) ≤
      (1566003076564351681379 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7220147100329 / 32000000000000 : ℝ) ≤
      (125000000000000 / 791674731336609 : ℝ) := by
    rw [show
        (125000000000000 / 791674731336609 : ℝ) =
          (3 / 40) / (2375024194009827 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4434522844404553221673 / 10000000000000000000000 : ℝ)) -
        6 * (1566003076564351681379 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7220147100329 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7220147100329 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2375024194009827 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4434522844404553221673 / 10000000000000000000000 : ℝ)) -
          6 * (1566003076564351681379 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7220147100329 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7220147100329 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7220147100329 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_273 :
    ((407779112086405099183 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14619333093774351598831 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((475565688117599 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4439097859537322069829 / 10000000000000000000000 : ℝ)) -
              6 * (1564186234996620458847 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2894882863549 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2894882863549 / 12800000000000 : ℝ)) =
      Real.log (15694882863549 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2894882863549 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2966882863549 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (407779112086405099183 / 2000000000000000000000 : ℝ) ≤
      Real.log (15694882863549 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2966882863549 / 12800000000000 : ℝ) ≤
      (-(14619333093774351598831 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2966882863549 / 12800000000000 : ℝ) = (2966882863549 / 1600000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2966882863549 / 1600000000000 : ℝ) ≤
            (6175082315225648401169 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (475565688117599 / 1000000000000000 : ℝ) ≤ Real.sqrt (2894882863549 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2894882863549 / 12800000000000 : ℝ) ≤ (4755656881175993 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2894882863549 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau335 :
    Real.arctan (4755656881175993 / 10000000000000000 : ℝ) ≤
      (4439097859537322069829 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4439097859537322069829 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4755656881175993 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4755656881175993 : ℝ) =
              (4755656881175993 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau335)
  have hz1 :
    (10000000000000000 / 4755656881175993 : ℝ) ≤
      1 / Real.sqrt (2894882863549 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4755656881175993 : ℝ) =
          1 / (4755656881175993 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 475565688117599 : ℝ) ≤
      (1564186234996620458847 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2894882863549 / 12800000000000 : ℝ) ≤
      (75000000000000 / 475565688117599 : ℝ) := by
    rw [show
        (75000000000000 / 475565688117599 : ℝ) =
          (3 / 40) / (475565688117599 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4439097859537322069829 / 10000000000000000000000 : ℝ)) -
        6 * (1564186234996620458847 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2894882863549 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2894882863549 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((475565688117599 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4439097859537322069829 / 10000000000000000000000 : ℝ)) -
          6 * (1564186234996620458847 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2894882863549 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2894882863549 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2894882863549 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_274 :
    ((2043242544342751051039 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7298179427416706252041 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4761258767849631 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4443665499155469865247 / 10000000000000000000000 : ℝ)) -
              6 * (390593925676510568093 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (906783402177 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (906783402177 / 4000000000000 : ℝ)) =
      Real.log (4906783402177 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((906783402177 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (929283402177 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2043242544342751051039 / 10000000000000000000000 : ℝ) ≤
      Real.log (4906783402177 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (929283402177 / 4000000000000 : ℝ) ≤
      (-(7298179427416706252041 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (929283402177 / 4000000000000 : ℝ) = (929283402177 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (929283402177 / 500000000000 : ℝ) ≤
            (3099028277083293747959 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4761258767849631 / 10000000000000000 : ℝ) ≤ Real.sqrt (906783402177 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (906783402177 / 4000000000000 : ℝ) ≤ (2380629383924817 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (906783402177 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau336 :
    Real.arctan (2380629383924817 / 5000000000000000 : ℝ) ≤
      (4443665499155469865247 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4443665499155469865247 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2380629383924817 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2380629383924817 : ℝ) =
              (2380629383924817 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau336)
  have hz1 :
    (5000000000000000 / 2380629383924817 : ℝ) ≤
      1 / Real.sqrt (906783402177 / 4000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2380629383924817 : ℝ) = 1 / (2380629383924817 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1587086255949877 : ℝ) ≤
      (390593925676510568093 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (906783402177 / 4000000000000 : ℝ) ≤
      (250000000000000 / 1587086255949877 : ℝ) := by
    rw [show
        (250000000000000 / 1587086255949877 : ℝ) =
          (3 / 40) / (4761258767849631 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4443665499155469865247 / 10000000000000000000000 : ℝ)) -
        6 * (390593925676510568093 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (906783402177 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (906783402177 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4761258767849631 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4443665499155469865247 / 10000000000000000000000 : ℝ)) -
          6 * (390593925676510568093 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (906783402177 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (906783402177 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (906783402177 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_275 :
    ((1023793819723797870683 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3643359319124335629843 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4766854071331891 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (88964515773027434811 / 200000000000000000000 : ℝ)) -
              6 * (390142860814587977897 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (14542654551919 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14542654551919 / 64000000000000 : ℝ)) =
      Real.log (78542654551919 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14542654551919 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14902654551919 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1023793819723797870683 / 5000000000000000000000 : ℝ) ≤
      Real.log (78542654551919 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14902654551919 / 64000000000000 : ℝ) ≤
      (-(3643359319124335629843 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14902654551919 / 64000000000000 : ℝ) = (14902654551919 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14902654551919 / 8000000000000 : ℝ) ≤
            (1555244533125664370157 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4766854071331891 / 10000000000000000 : ℝ) ≤
      Real.sqrt (14542654551919 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14542654551919 / 64000000000000 : ℝ) ≤ (2383427035665947 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14542654551919 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau337 :
    Real.arctan (2383427035665947 / 5000000000000000 : ℝ) ≤
      (88964515773027434811 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (88964515773027434811 / 200000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2383427035665947 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2383427035665947 : ℝ) =
              (2383427035665947 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau337)
  have hz1 :
    (5000000000000000 / 2383427035665947 : ℝ) ≤
      1 / Real.sqrt (14542654551919 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2383427035665947 : ℝ) = 1 / (2383427035665947 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4766854071331891 : ℝ) ≤
      (390142860814587977897 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (14542654551919 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4766854071331891 : ℝ) := by
    rw [show
        (750000000000000 / 4766854071331891 : ℝ) =
          (3 / 40) / (4766854071331891 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (88964515773027434811 / 200000000000000000000 : ℝ)) -
        6 * (390142860814587977897 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14542654551919 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14542654551919 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4766854071331891 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (88964515773027434811 / 200000000000000000000 : ℝ)) -
          6 * (390142860814587977897 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (14542654551919 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14542654551919 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14542654551919 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_276 :
    ((2051930847387254958117 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14550568117905186109883 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((95448856295551 / 200000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2226389376636543872639 / 5000000000000000000000 : ℝ)) -
              6 * (1558773420513176924499 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7288387334503 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7288387334503 / 32000000000000 : ℝ)) =
      Real.log (39288387334503 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7288387334503 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7468387334503 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2051930847387254958117 / 10000000000000000000000 : ℝ) ≤
      Real.log (39288387334503 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7468387334503 / 32000000000000 : ℝ) ≤
      (-(14550568117905186109883 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7468387334503 / 32000000000000 : ℝ) = (7468387334503 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7468387334503 / 4000000000000 : ℝ) ≤
            (6243847291094813890117 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (95448856295551 / 200000000000000 : ℝ) ≤ Real.sqrt (7288387334503 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7288387334503 / 32000000000000 : ℝ) ≤ (4772442814777553 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7288387334503 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau338 :
    Real.arctan (4772442814777553 / 10000000000000000 : ℝ) ≤
      (2226389376636543872639 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2226389376636543872639 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4772442814777553 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4772442814777553 : ℝ) =
              (4772442814777553 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau338)
  have hz1 :
    (10000000000000000 / 4772442814777553 : ℝ) ≤
      1 / Real.sqrt (7288387334503 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4772442814777553 : ℝ) =
          1 / (4772442814777553 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (15000000000000 / 95448856295551 : ℝ) ≤
      (1558773420513176924499 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7288387334503 / 32000000000000 : ℝ) ≤
      (15000000000000 / 95448856295551 : ℝ) := by
    rw [show
        (15000000000000 / 95448856295551 : ℝ) = (3 / 40) / (95448856295551 / 200000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2226389376636543872639 / 5000000000000000000000 : ℝ)) -
        6 * (1558773420513176924499 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7288387334503 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7288387334503 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((95448856295551 / 200000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2226389376636543872639 / 5000000000000000000000 : ℝ)) -
          6 * (1558773420513176924499 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7288387334503 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7288387334503 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7288387334503 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
