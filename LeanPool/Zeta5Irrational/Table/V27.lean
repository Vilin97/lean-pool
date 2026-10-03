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

/-! # V27: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_325 :
    ((2602736867247839204543 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5971596284766294893433 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2726192802200519 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ))) -
              6 * (683483096073199743303 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (19026245618611 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19026245618611 / 64000000000000 : ℝ)) =
      Real.log (83026245618611 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19026245618611 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19386245618611 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2602736867247839204543 / 10000000000000000000000 : ℝ) ≤
      Real.log (83026245618611 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19386245618611 / 64000000000000 : ℝ) ≤
      (-(5971596284766294893433 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19386245618611 / 64000000000000 : ℝ) = (19386245618611 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19386245618611 / 16000000000000 : ℝ) ≤
            (959875518233705106567 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2726192802200519 / 5000000000000000 : ℝ) ≤ Real.sqrt (19026245618611 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19026245618611 / 64000000000000 : ℝ) ≤
      (5452385604401041 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19026245618611 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau422 :
    Real.arctan (5452385604401041 / 21389842350931802 : ℝ) ≤
      (2495901233890856705717 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau421 :
    Real.arctan (5452385604401041 / 10000000000000000 : ℝ) ≤
      (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5694921175465901 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5452385604401041 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5452385604401041 / 10000000000000000 : ℝ) /
                (1 + (5694921175465901 / 5000000000000000 : ℝ)) =
              (5452385604401041 / 21389842350931802 : ℝ)
            by
        norm_num];
        exact hau422)
  have hat1 :
    (Real.pi / 2 - (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5452385604401041 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5452385604401041 : ℝ) =
              (5452385604401041 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau421)
  have hz1 :
    (10000000000000000 / 5452385604401041 : ℝ) ≤
      1 / Real.sqrt (19026245618611 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5452385604401041 : ℝ) =
          1 / (5452385604401041 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2726192802200519 : ℝ) ≤
      (683483096073199743303 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19026245618611 / 64000000000000 : ℝ) ≤
      (375000000000000 / 2726192802200519 : ℝ) := by
    rw [show
        (375000000000000 / 2726192802200519 : ℝ) =
          (3 / 40) / (2726192802200519 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ))) -
        6 * (683483096073199743303 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19026245618611 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19026245618611 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2726192802200519 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ))) -
          6 * (683483096073199743303 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (19026245618611 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19026245618611 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19026245618611 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_326 :
    ((651854409488761182881 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11923161429885025563023 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1364488135098277 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ))) -
              6 * (1365589208491496565637 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1525209391779 / 5120000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1525209391779 / 5120000000000 : ℝ)) =
      Real.log (6645209391779 / 5120000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1525209391779 / 5120000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1554009391779 / 5120000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (651854409488761182881 / 2500000000000000000000 : ℝ) ≤
      Real.log (6645209391779 / 5120000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1554009391779 / 5120000000000 : ℝ) ≤
      (-(11923161429885025563023 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1554009391779 / 5120000000000 : ℝ) = (1554009391779 / 1280000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1554009391779 / 1280000000000 : ℝ) ≤
            (1939782176114974436977 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1364488135098277 / 2500000000000000 : ℝ) ≤ Real.sqrt (1525209391779 / 5120000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1525209391779 / 5120000000000 : ℝ) ≤ (5457952540393111 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1525209391779 / 5120000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau424 :
    Real.arctan (5457952540393111 / 21392508324911752 : ℝ) ≤
      (2498046341966979991561 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau423 :
    Real.arctan (5457952540393111 / 10000000000000000 : ℝ) ≤
      (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1424063540613969 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (5457952540393111 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5457952540393111 / 10000000000000000 : ℝ) /
                (1 + (1424063540613969 / 1250000000000000 : ℝ)) =
              (5457952540393111 / 21392508324911752 : ℝ)
            by
        norm_num];
        exact hau424)
  have hat1 :
    (Real.pi / 2 - (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5457952540393111 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5457952540393111 : ℝ) =
              (5457952540393111 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau423)
  have hz1 :
    (10000000000000000 / 5457952540393111 : ℝ) ≤
      1 / Real.sqrt (1525209391779 / 5120000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5457952540393111 : ℝ) =
          1 / (5457952540393111 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1364488135098277 : ℝ) ≤
      (1365589208491496565637 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1525209391779 / 5120000000000 : ℝ) ≤
      (187500000000000 / 1364488135098277 : ℝ) := by
    rw [show
        (187500000000000 / 1364488135098277 : ℝ) =
          (3 / 40) / (1364488135098277 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ))) -
        6 * (1365589208491496565637 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1525209391779 / 5120000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1525209391779 / 5120000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1364488135098277 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ))) -
          6 * (1365589208491496565637 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1525209391779 / 5120000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1525209391779 / 5120000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1525209391779 / 5120000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_327 :
    ((2612096218725827974741 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5951585167346387345697 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((27317569020361 / 50000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ))) -
              6 * (341054094455857365227 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2387998646983 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2387998646983 / 8000000000000 : ℝ)) =
      Real.log (10387998646983 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2387998646983 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2432998646983 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2612096218725827974741 / 10000000000000000000000 : ℝ) ≤
      Real.log (10387998646983 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2432998646983 / 8000000000000 : ℝ) ≤
      (-(5951585167346387345697 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2432998646983 / 8000000000000 : ℝ) = (2432998646983 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2432998646983 / 2000000000000 : ℝ) ≤
            (979886635653612654303 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (27317569020361 / 50000000000000 : ℝ) ≤ Real.sqrt (2387998646983 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2387998646983 / 8000000000000 : ℝ) ≤ (5463513804072203 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2387998646983 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau426 :
    Real.arctan (5463513804072203 / 21395173675170005 : ℝ) ≤
      (2500188261746333242647 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau425 :
    Real.arctan (5463513804072203 / 10000000000000000 : ℝ) ≤
      (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2279034735034001 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5463513804072203 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5463513804072203 / 10000000000000000 : ℝ) /
                (1 + (2279034735034001 / 2000000000000000 : ℝ)) =
              (5463513804072203 / 21395173675170005 : ℝ)
            by
        norm_num];
        exact hau426)
  have hat1 :
    (Real.pi / 2 - (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5463513804072203 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5463513804072203 : ℝ) =
              (5463513804072203 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau425)
  have hz1 :
    (10000000000000000 / 5463513804072203 : ℝ) ≤
      1 / Real.sqrt (2387998646983 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5463513804072203 : ℝ) =
          1 / (5463513804072203 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (3750000000000 / 27317569020361 : ℝ) ≤
      (341054094455857365227 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2387998646983 / 8000000000000 : ℝ) ≤
      (3750000000000 / 27317569020361 : ℝ) := by
    rw [show
        (3750000000000 / 27317569020361 : ℝ) = (3 / 40) / (27317569020361 / 50000000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ))) -
        6 * (341054094455857365227 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2387998646983 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2387998646983 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((27317569020361 / 50000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ))) -
          6 * (341054094455857365227 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (2387998646983 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2387998646983 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2387998646983 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_328 :
    ((2616772611608389628563 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11883219124168659191989 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1367267353185529 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ))) -
              6 * (681423839653867688303 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (38285721908981 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38285721908981 / 128000000000000 : ℝ)) =
      Real.log (166285721908981 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38285721908981 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39005721908981 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2616772611608389628563 / 10000000000000000000000 : ℝ) ≤
      Real.log (166285721908981 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39005721908981 / 128000000000000 : ℝ) ≤
      (-(11883219124168659191989 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (39005721908981 / 128000000000000 : ℝ) = (39005721908981 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39005721908981 / 32000000000000 : ℝ) ≤
            (1979724481831340808011 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1367267353185529 / 2500000000000000 : ℝ) ≤
      Real.sqrt (38285721908981 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38285721908981 / 128000000000000 : ℝ) ≤
      (5469069412742119 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38285721908981 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau428 :
    Real.arctan (5469069412742119 / 21397838402144127 : ℝ) ≤
      (2502327002872303514111 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau427 :
    Real.arctan (5469069412742119 / 10000000000000000 : ℝ) ≤
      (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11397838402144127 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5469069412742119 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5469069412742119 / 10000000000000000 : ℝ) /
                (1 + (11397838402144127 / 10000000000000000 : ℝ)) =
              (5469069412742119 / 21397838402144127 : ℝ)
            by
        norm_num];
        exact hau428)
  have hat1 :
    (Real.pi / 2 - (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5469069412742119 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5469069412742119 : ℝ) =
              (5469069412742119 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau427)
  have hz1 :
    (10000000000000000 / 5469069412742119 : ℝ) ≤
      1 / Real.sqrt (38285721908981 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5469069412742119 : ℝ) =
          1 / (5469069412742119 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1367267353185529 : ℝ) ≤
      (681423839653867688303 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38285721908981 / 128000000000000 : ℝ) ≤
      (187500000000000 / 1367267353185529 : ℝ) := by
    rw [show
        (187500000000000 / 1367267353185529 : ℝ) =
          (3 / 40) / (1367267353185529 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ))) -
        6 * (681423839653867688303 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38285721908981 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38285721908981 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1367267353185529 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ))) -
          6 * (681423839653867688303 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (38285721908981 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38285721908981 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38285721908981 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_329 :
    ((262144681864805827297 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11863307639479982018991 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1094923876723771 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ))) -
              6 * (340370773063998395589 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (19181732733117 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19181732733117 / 64000000000000 : ℝ)) =
      Real.log (83181732733117 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19181732733117 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19541732733117 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (262144681864805827297 / 1000000000000000000000 : ℝ) ≤
      Real.log (83181732733117 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19541732733117 / 64000000000000 : ℝ) ≤
      (-(11863307639479982018991 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19541732733117 / 64000000000000 : ℝ) = (19541732733117 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19541732733117 / 16000000000000 : ℝ) ≤
            (1999635966520017981009 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1094923876723771 / 2000000000000000 : ℝ) ≤ Real.sqrt (19181732733117 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19181732733117 / 64000000000000 : ℝ) ≤ (2737309691809429 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19181732733117 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau430 :
    Real.arctan (5474619383618858 / 21400502506271173 : ℝ) ≤
      (1252231287470484669311 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau429 :
    Real.arctan (2737309691809429 / 5000000000000000 : ℝ) ≤
      (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11400502506271173 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2737309691809429 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2737309691809429 / 5000000000000000 : ℝ) /
                (1 + (11400502506271173 / 10000000000000000 : ℝ)) =
              (5474619383618858 / 21400502506271173 : ℝ)
            by
        norm_num];
        exact hau430)
  have hat1 :
    (Real.pi / 2 - (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2737309691809429 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2737309691809429 : ℝ) =
              (2737309691809429 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau429)
  have hz1 :
    (5000000000000000 / 2737309691809429 : ℝ) ≤
      1 / Real.sqrt (19181732733117 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2737309691809429 : ℝ) = 1 / (2737309691809429 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1094923876723771 : ℝ) ≤
      (340370773063998395589 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19181732733117 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1094923876723771 : ℝ) := by
    rw [show
        (150000000000000 / 1094923876723771 : ℝ) =
          (3 / 40) / (1094923876723771 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ))) -
        6 * (340370773063998395589 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19181732733117 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19181732733117 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1094923876723771 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ))) -
          6 * (340370773063998395589 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (19181732733117 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19181732733117 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19181732733117 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_330 :
    ((525223768377459148197 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11843435722740940104459 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1370040933457811 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ))) -
              6 * (272024519224901943929 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (38441209023487 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38441209023487 / 128000000000000 : ℝ)) =
      Real.log (166441209023487 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38441209023487 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39161209023487 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (525223768377459148197 / 2000000000000000000000 : ℝ) ≤
      Real.log (166441209023487 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39161209023487 / 128000000000000 : ℝ) ≤
      (-(11843435722740940104459 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (39161209023487 / 128000000000000 : ℝ) = (39161209023487 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39161209023487 / 32000000000000 : ℝ) ≤
            (2019507883259059895541 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1370040933457811 / 2500000000000000 : ℝ) ≤
      Real.sqrt (38441209023487 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38441209023487 / 128000000000000 : ℝ) ≤
      (5480163733831247 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38441209023487 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau432 :
    Real.arctan (5480163733831247 / 21403165987987687 : ℝ) ≤
      (1253297493750716190239 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau431 :
    Real.arctan (5480163733831247 / 10000000000000000 : ℝ) ≤
      (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11403165987987687 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5480163733831247 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5480163733831247 / 10000000000000000 : ℝ) /
                (1 + (11403165987987687 / 10000000000000000 : ℝ)) =
              (5480163733831247 / 21403165987987687 : ℝ)
            by
        norm_num];
        exact hau432)
  have hat1 :
    (Real.pi / 2 - (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5480163733831247 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5480163733831247 : ℝ) =
              (5480163733831247 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau431)
  have hz1 :
    (10000000000000000 / 5480163733831247 : ℝ) ≤
      1 / Real.sqrt (38441209023487 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5480163733831247 : ℝ) =
          1 / (5480163733831247 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1370040933457811 : ℝ) ≤
      (272024519224901943929 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38441209023487 / 128000000000000 : ℝ) ≤
      (187500000000000 / 1370040933457811 : ℝ) := by
    rw [show
        (187500000000000 / 1370040933457811 : ℝ) =
          (3 / 40) / (1370040933457811 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ))) -
        6 * (272024519224901943929 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38441209023487 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38441209023487 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1370040933457811 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ))) -
          6 * (272024519224901943929 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (38441209023487 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38441209023487 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38441209023487 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_331 :
    ((2630788683365702473583 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11823603217005112636329 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5485702480421547 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ))) -
              6 * (135876617051301854297 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (1925947629037 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1925947629037 / 6400000000000 : ℝ)) =
      Real.log (8325947629037 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1925947629037 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1961947629037 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2630788683365702473583 / 10000000000000000000000 : ℝ) ≤
      Real.log (8325947629037 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1961947629037 / 6400000000000 : ℝ) ≤
      (-(11823603217005112636329 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1961947629037 / 6400000000000 : ℝ) = (1961947629037 / 1600000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1961947629037 / 1600000000000 : ℝ) ≤
            (2039340388994887363671 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5485702480421547 / 10000000000000000 : ℝ) ≤ Real.sqrt (1925947629037 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1925947629037 / 6400000000000 : ℝ) ≤ (109714049608431 / 200000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1925947629037 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau434 :
    Real.arctan (914283746736925 / 3567638141288284 : ℝ) ≤
      (2508724250056138755739 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau433 :
    Real.arctan (109714049608431 / 200000000000000 : ℝ) ≤
      (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1425728605966213 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (109714049608431 / 200000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (109714049608431 / 200000000000000 : ℝ) /
                (1 + (1425728605966213 / 1250000000000000 : ℝ)) =
              (914283746736925 / 3567638141288284 : ℝ)
            by
        norm_num];
        exact hau434)
  have hat1 :
    (Real.pi / 2 - (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (200000000000000 / 109714049608431 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 109714049608431 : ℝ) =
              (109714049608431 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau433)
  have hz1 :
    (200000000000000 / 109714049608431 : ℝ) ≤ 1 / Real.sqrt (1925947629037 / 6400000000000 : ℝ) :=
  by
    rw [show (200000000000000 / 109714049608431 : ℝ) = 1 / (109714049608431 / 200000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1828567493473849 : ℝ) ≤
      (135876617051301854297 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1925947629037 / 6400000000000 : ℝ) ≤
      (250000000000000 / 1828567493473849 : ℝ) := by
    rw [show
        (250000000000000 / 1828567493473849 : ℝ) =
          (3 / 40) / (5485702480421547 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ))) -
        6 * (135876617051301854297 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1925947629037 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1925947629037 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5485702480421547 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ))) -
          6 * (135876617051301854297 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (1925947629037 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1925947629037 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1925947629037 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_332 :
    ((66003045729603764453 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(736503488463111140191 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1099352646095163 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (314121670365840661703 / 1250000000000000000000 : ℝ))) -
              6 * (678032724979199444369 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (19337219847623 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19337219847623 / 64000000000000 : ℝ)) =
      Real.log (83337219847623 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19337219847623 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19697219847623 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (66003045729603764453 / 250000000000000000000 : ℝ) ≤
      Real.log (83337219847623 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19697219847623 / 64000000000000 : ℝ) ≤
      (-(736503488463111140191 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19697219847623 / 64000000000000 : ℝ) = (19697219847623 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19697219847623 / 16000000000000 : ℝ) ≤
            (129930486911888859809 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1099352646095163 / 2000000000000000 : ℝ) ≤ Real.sqrt (19337219847623 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19337219847623 / 64000000000000 : ℝ) ≤ (2748381615237909 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19337219847623 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau436 :
    Real.arctan (916127205079303 / 3568525450505307 : ℝ) ≤
      (314121670365840661703 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau435 :
    Real.arctan (2748381615237909 / 5000000000000000 : ℝ) ≤
      (2 * (314121670365840661703 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5705576351515921 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2748381615237909 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2748381615237909 / 5000000000000000 : ℝ) /
                (1 + (5705576351515921 / 5000000000000000 : ℝ)) =
              (916127205079303 / 3568525450505307 : ℝ)
            by
        norm_num];
        exact hau436)
  have hat1 :
    (Real.pi / 2 - (2 * (314121670365840661703 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2748381615237909 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2748381615237909 : ℝ) =
              (2748381615237909 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau435)
  have hz1 :
    (5000000000000000 / 2748381615237909 : ℝ) ≤
      1 / Real.sqrt (19337219847623 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2748381615237909 : ℝ) = 1 / (2748381615237909 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 366450882031721 : ℝ) ≤
      (678032724979199444369 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19337219847623 / 64000000000000 : ℝ) ≤
      (50000000000000 / 366450882031721 : ℝ) := by
    rw [show
        (50000000000000 / 366450882031721 : ℝ) =
          (3 / 40) / (1099352646095163 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (314121670365840661703 / 1250000000000000000000 : ℝ))) -
        6 * (678032724979199444369 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19337219847623 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19337219847623 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1099352646095163 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (314121670365840661703 / 1250000000000000000000 : ℝ))) -
          6 * (678032724979199444369 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (19337219847623 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19337219847623 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19337219847623 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_333 :
    ((2649446272363180973399 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2348932839525893305633 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5507801768411671 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ))) -
              6 * (270676154042019708727 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (4853740851219 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4853740851219 / 16000000000000 : ℝ)) =
      Real.log (20853740851219 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4853740851219 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4943740851219 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2649446272363180973399 / 10000000000000000000000 : ℝ) ≤
      Real.log (20853740851219 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4943740851219 / 16000000000000 : ℝ) ≤
      (-(2348932839525893305633 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4943740851219 / 16000000000000 : ℝ) = (4943740851219 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4943740851219 / 4000000000000 : ℝ) ≤
            (423655881674106694367 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5507801768411671 / 10000000000000000 : ℝ) ≤ Real.sqrt (4853740851219 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4853740851219 / 16000000000000 : ℝ) ≤ (2753900884205837 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4853740851219 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau438 :
    Real.arctan (5507801768411674 / 21416474075655703 : ℝ) ≤
      (1258604994325691642003 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau437 :
    Real.arctan (2753900884205837 / 5000000000000000 : ℝ) ≤
      (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11416474075655703 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2753900884205837 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2753900884205837 / 5000000000000000 : ℝ) /
                (1 + (11416474075655703 / 10000000000000000 : ℝ)) =
              (5507801768411674 / 21416474075655703 : ℝ)
            by
        norm_num];
        exact hau438)
  have hat1 :
    (Real.pi / 2 - (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2753900884205837 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2753900884205837 : ℝ) =
              (2753900884205837 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau437)
  have hz1 :
    (5000000000000000 / 2753900884205837 : ℝ) ≤
      1 / Real.sqrt (4853740851219 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2753900884205837 : ℝ) = 1 / (2753900884205837 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5507801768411671 : ℝ) ≤
      (270676154042019708727 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4853740851219 / 16000000000000 : ℝ) ≤
      (750000000000000 / 5507801768411671 : ℝ) := by
    rw [show
        (750000000000000 / 5507801768411671 : ℝ) =
          (3 / 40) / (5507801768411671 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ))) -
        6 * (270676154042019708727 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4853740851219 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4853740851219 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5507801768411671 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ))) -
          6 * (270676154042019708727 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (4853740851219 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4853740851219 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4853740851219 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_334 :
    ((166172626819820649641 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2926356785290338176897 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5518818227512711 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ))) -
              6 * (1350711973100143615783 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19492706962129 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19492706962129 / 64000000000000 : ℝ)) =
      Real.log (83492706962129 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19492706962129 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19852706962129 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (166172626819820649641 / 625000000000000000000 : ℝ) ≤
      Real.log (83492706962129 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19852706962129 / 64000000000000 : ℝ) ≤
      (-(2926356785290338176897 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19852706962129 / 64000000000000 : ℝ) = (19852706962129 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19852706962129 / 16000000000000 : ℝ) ≤
            (539379116209661823103 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5518818227512711 / 10000000000000000 : ℝ) ≤
      Real.sqrt (19492706962129 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19492706962129 / 64000000000000 : ℝ) ≤ (2759409113756357 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19492706962129 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau440 :
    Real.arctan (2759409113756357 / 10710896484535649 : ℝ) ≤
      (2521434201602609004749 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau439 :
    Real.arctan (2759409113756357 / 5000000000000000 : ℝ) ≤
      (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5710896484535649 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2759409113756357 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2759409113756357 / 5000000000000000 : ℝ) /
                (1 + (5710896484535649 / 5000000000000000 : ℝ)) =
              (2759409113756357 / 10710896484535649 : ℝ)
            by
        norm_num];
        exact hau440)
  have hat1 :
    (Real.pi / 2 - (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2759409113756357 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2759409113756357 : ℝ) =
              (2759409113756357 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau439)
  have hz1 :
    (5000000000000000 / 2759409113756357 : ℝ) ≤
      1 / Real.sqrt (19492706962129 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2759409113756357 : ℝ) = 1 / (2759409113756357 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5518818227512711 : ℝ) ≤
      (1350711973100143615783 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19492706962129 / 64000000000000 : ℝ) ≤
      (750000000000000 / 5518818227512711 : ℝ) := by
    rw [show
        (750000000000000 / 5518818227512711 : ℝ) =
          (3 / 40) / (5518818227512711 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ))) -
        6 * (1350711973100143615783 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19492706962129 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19492706962129 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5518818227512711 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ))) -
          6 * (1350711973100143615783 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (19492706962129 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19492706962129 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19492706962129 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_335 :
    ((533613823123012619069 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(729146464864790530219 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((345613296233431 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ))) -
              6 * (337014725658869163649 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (9785225259691 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9785225259691 / 32000000000000 : ℝ)) =
      Real.log (41785225259691 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9785225259691 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9965225259691 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (533613823123012619069 / 2000000000000000000000 : ℝ) ≤
      Real.log (41785225259691 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9965225259691 / 32000000000000 : ℝ) ≤
      (-(729146464864790530219 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9965225259691 / 32000000000000 : ℝ) = (9965225259691 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9965225259691 / 8000000000000 : ℝ) ≤
            (137287510510209469781 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (345613296233431 / 625000000000000 : ℝ) ≤ Real.sqrt (9785225259691 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9785225259691 / 32000000000000 : ℝ) ≤ (5529812739734899 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9785225259691 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau442 :
    Real.arctan (5529812739734899 / 21427109386740566 : ℝ) ≤
      (1262823037718319180193 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau441 :
    Real.arctan (5529812739734899 / 10000000000000000 : ℝ) ≤
      (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5713554693370283 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5529812739734899 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5529812739734899 / 10000000000000000 : ℝ) /
                (1 + (5713554693370283 / 5000000000000000 : ℝ)) =
              (5529812739734899 / 21427109386740566 : ℝ)
            by
        norm_num];
        exact hau442)
  have hat1 :
    (Real.pi / 2 - (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5529812739734899 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5529812739734899 : ℝ) =
              (5529812739734899 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau441)
  have hz1 :
    (10000000000000000 / 5529812739734899 : ℝ) ≤
      1 / Real.sqrt (9785225259691 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5529812739734899 : ℝ) =
          1 / (5529812739734899 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 345613296233431 : ℝ) ≤
      (337014725658869163649 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9785225259691 / 32000000000000 : ℝ) ≤
      (46875000000000 / 345613296233431 : ℝ) := by
    rw [show
        (46875000000000 / 345613296233431 : ℝ) =
          (3 / 40) / (345613296233431 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ))) -
        6 * (337014725658869163649 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9785225259691 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9785225259691 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((345613296233431 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ))) -
          6 * (337014725658869163649 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (9785225259691 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9785225259691 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9785225259691 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_336 :
    ((1338683773990469618213 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2906852973399345608809 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((554078543572499 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ))) -
              6 * (672710702479827681713 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3929638815327 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3929638815327 / 12800000000000 : ℝ)) =
      Real.log (16729638815327 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3929638815327 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4001638815327 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1338683773990469618213 / 5000000000000000000000 : ℝ) ≤
      Real.log (16729638815327 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4001638815327 / 12800000000000 : ℝ) ≤
      (-(2906852973399345608809 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4001638815327 / 12800000000000 : ℝ) = (4001638815327 / 3200000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4001638815327 / 3200000000000 : ℝ) ≤
            (558882928100654391191 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (554078543572499 / 1000000000000000 : ℝ) ≤ Real.sqrt (3929638815327 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3929638815327 / 12800000000000 : ℝ) ≤ (5540785435724993 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3929638815327 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau444 :
    Real.arctan (5540785435724993 / 21432423332117393 : ℝ) ≤
      (1264922841551584207157 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau443 :
    Real.arctan (5540785435724993 / 10000000000000000 : ℝ) ≤
      (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11432423332117393 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5540785435724993 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5540785435724993 / 10000000000000000 : ℝ) /
                (1 + (11432423332117393 / 10000000000000000 : ℝ)) =
              (5540785435724993 / 21432423332117393 : ℝ)
            by
        norm_num];
        exact hau444)
  have hat1 :
    (Real.pi / 2 - (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5540785435724993 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5540785435724993 : ℝ) =
              (5540785435724993 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau443)
  have hz1 :
    (10000000000000000 / 5540785435724993 : ℝ) ≤
      1 / Real.sqrt (3929638815327 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5540785435724993 : ℝ) =
          1 / (5540785435724993 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 554078543572499 : ℝ) ≤
      (672710702479827681713 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3929638815327 / 12800000000000 : ℝ) ≤
      (75000000000000 / 554078543572499 : ℝ) := by
    rw [show
        (75000000000000 / 554078543572499 : ℝ) =
          (3 / 40) / (554078543572499 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ))) -
        6 * (672710702479827681713 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3929638815327 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3929638815327 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((554078543572499 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ))) -
          6 * (672710702479827681713 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3929638815327 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3929638815327 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3929638815327 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
