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

/-! # V28: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_337 :
    ((537331468458756497103 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5794315664138754364461 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1387934111209669 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1267016548427454690201 / 5000000000000000000000 : ℝ))) -
              6 * (1342799328315371089453 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (616435551059 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (616435551059 / 2000000000000 : ℝ)) =
      Real.log (2616435551059 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((616435551059 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (627685551059 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (537331468458756497103 / 2000000000000000000000 : ℝ) ≤
      Real.log (2616435551059 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (627685551059 / 2000000000000 : ℝ) ≤
      (-(5794315664138754364461 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (627685551059 / 2000000000000 : ℝ) = (627685551059 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (627685551059 / 500000000000 : ℝ) ≤
            (1137156138861245635539 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1387934111209669 / 2500000000000000 : ℝ) ≤ Real.sqrt (616435551059 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (616435551059 / 2000000000000 : ℝ) ≤ (5551736444838679 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (616435551059 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau446 :
    Real.arctan (5551736444838679 / 21437734808647645 : ℝ) ≤
      (1267016548427454690201 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau445 :
    Real.arctan (5551736444838679 / 10000000000000000 : ℝ) ≤
      (2 * (1267016548427454690201 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2287546961729529 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5551736444838679 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5551736444838679 / 10000000000000000 : ℝ) /
                (1 + (2287546961729529 / 2000000000000000 : ℝ)) =
              (5551736444838679 / 21437734808647645 : ℝ)
            by
        norm_num];
        exact hau446)
  have hat1 :
    (Real.pi / 2 - (2 * (1267016548427454690201 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5551736444838679 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5551736444838679 : ℝ) =
              (5551736444838679 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau445)
  have hz1 :
    (10000000000000000 / 5551736444838679 : ℝ) ≤
      1 / Real.sqrt (616435551059 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5551736444838679 : ℝ) =
          1 / (5551736444838679 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1387934111209669 : ℝ) ≤
      (1342799328315371089453 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (616435551059 / 2000000000000 : ℝ) ≤
      (187500000000000 / 1387934111209669 : ℝ) := by
    rw [show
        (187500000000000 / 1387934111209669 : ℝ) =
          (3 / 40) / (1387934111209669 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1267016548427454690201 / 5000000000000000000000 : ℝ))) -
        6 * (1342799328315371089453 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (616435551059 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (616435551059 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1387934111209669 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1267016548427454690201 / 5000000000000000000000 : ℝ))) -
          6 * (1342799328315371089453 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (616435551059 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (616435551059 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (616435551059 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_338 :
    ((1347969257293923422131 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11550000575388243838883 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1112533179031669 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1269104194128484300137 / 5000000000000000000000 : ℝ))) -
              6 * (670096261503884641029 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (19803681191141 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19803681191141 / 64000000000000 : ℝ)) =
      Real.log (83803681191141 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19803681191141 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20163681191141 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1347969257293923422131 / 5000000000000000000000 : ℝ) ≤
      Real.log (83803681191141 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20163681191141 / 64000000000000 : ℝ) ≤
      (-(11550000575388243838883 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (20163681191141 / 64000000000000 : ℝ) = (20163681191141 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20163681191141 / 16000000000000 : ℝ) ≤
            (2312943030611756161117 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1112533179031669 / 2000000000000000 : ℝ) ≤ Real.sqrt (19803681191141 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19803681191141 / 64000000000000 : ℝ) ≤ (1390666473789587 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19803681191141 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau448 :
    Real.arctan (5562665895158348 / 21443043819769187 : ℝ) ≤
      (1269104194128484300137 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau447 :
    Real.arctan (1390666473789587 / 2500000000000000 : ℝ) ≤
      (2 * (1269104194128484300137 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11443043819769187 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1390666473789587 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1390666473789587 / 2500000000000000 : ℝ) /
                (1 + (11443043819769187 / 10000000000000000 : ℝ)) =
              (5562665895158348 / 21443043819769187 : ℝ)
            by
        norm_num];
        exact hau448)
  have hat1 :
    (Real.pi / 2 - (2 * (1269104194128484300137 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1390666473789587 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1390666473789587 : ℝ) =
              (1390666473789587 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau447)
  have hz1 :
    (2500000000000000 / 1390666473789587 : ℝ) ≤
      1 / Real.sqrt (19803681191141 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1390666473789587 : ℝ) = 1 / (1390666473789587 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1112533179031669 : ℝ) ≤
      (670096261503884641029 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19803681191141 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1112533179031669 : ℝ) := by
    rw [show
        (150000000000000 / 1112533179031669 : ℝ) =
          (3 / 40) / (1112533179031669 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1269104194128484300137 / 5000000000000000000000 : ℝ))) -
        6 * (670096261503884641029 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19803681191141 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19803681191141 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1112533179031669 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1269104194128484300137 / 5000000000000000000000 : ℝ))) -
          6 * (670096261503884641029 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (19803681191141 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19803681191141 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19803681191141 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_339 :
    ((1352605540426391349941 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11511518481907533559663 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5573573913510577 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (79449113381127256143 / 312500000000000000000 : ℝ))) -
              6 * (167200105171068611039 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (9940712374197 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9940712374197 / 32000000000000 : ℝ)) =
      Real.log (41940712374197 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9940712374197 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10120712374197 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1352605540426391349941 / 5000000000000000000000 : ℝ) ≤
      Real.log (41940712374197 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10120712374197 / 32000000000000 : ℝ) ≤
      (-(11511518481907533559663 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (10120712374197 / 32000000000000 : ℝ) = (10120712374197 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10120712374197 / 8000000000000 : ℝ) ≤
            (2351425124092466440337 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5573573913510577 / 10000000000000000 : ℝ) ≤ Real.sqrt (9940712374197 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9940712374197 / 32000000000000 : ℝ) ≤ (278678695675529 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9940712374197 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau450 :
    Real.arctan (1393393478377645 / 5362087592227979 : ℝ) ≤
      (79449113381127256143 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau449 :
    Real.arctan (278678695675529 / 500000000000000 : ℝ) ≤
      (2 * (79449113381127256143 / 312500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2862087592227979 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (278678695675529 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (278678695675529 / 500000000000000 : ℝ) /
                (1 + (2862087592227979 / 2500000000000000 : ℝ)) =
              (1393393478377645 / 5362087592227979 : ℝ)
            by
        norm_num];
        exact hau450)
  have hat1 :
    (Real.pi / 2 - (2 * (79449113381127256143 / 312500000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 278678695675529 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 278678695675529 : ℝ) =
              (278678695675529 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau449)
  have hz1 :
    (500000000000000 / 278678695675529 : ℝ) ≤
      1 / Real.sqrt (9940712374197 / 32000000000000 : ℝ) := by
    rw [show (500000000000000 / 278678695675529 : ℝ) = 1 / (278678695675529 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5573573913510577 : ℝ) ≤
      (167200105171068611039 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9940712374197 / 32000000000000 : ℝ) ≤
      (750000000000000 / 5573573913510577 : ℝ) := by
    rw [show
        (750000000000000 / 5573573913510577 : ℝ) =
          (3 / 40) / (5573573913510577 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (79449113381127256143 / 312500000000000000000 : ℝ))) -
        6 * (167200105171068611039 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9940712374197 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9940712374197 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5573573913510577 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (79449113381127256143 / 312500000000000000000 : ℝ))) -
          6 * (167200105171068611039 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (9940712374197 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9940712374197 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9940712374197 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_340 :
    ((680932614757960827541 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11434995727182164588973 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((349707884715169 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (510132446778923655351 / 2000000000000000000000 : ℝ))) -
              6 * (1332462268344726654813 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (200369118629 / 640000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (200369118629 / 640000000000 : ℝ)) =
      Real.log (840369118629 / 640000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((200369118629 / 640000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (203969118629 / 640000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (680932614757960827541 / 2500000000000000000000 : ℝ) ≤
      Real.log (840369118629 / 640000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (203969118629 / 640000000000 : ℝ) ≤
      (-(11434995727182164588973 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (203969118629 / 640000000000 : ℝ) = (203969118629 / 160000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (203969118629 / 160000000000 : ℝ) ≤
            (2427947878817835411027 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (349707884715169 / 625000000000000 : ℝ) ≤ Real.sqrt (200369118629 / 640000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (200369118629 / 640000000000 : ℝ) ≤ (5595326155442707 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (200369118629 / 640000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau452 :
    Real.arctan (5595326155442707 / 21458956094940814 : ℝ) ≤
      (510132446778923655351 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau451 :
    Real.arctan (5595326155442707 / 10000000000000000 : ℝ) ≤
      (2 * (510132446778923655351 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5729478047470407 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5595326155442707 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5595326155442707 / 10000000000000000 : ℝ) /
                (1 + (5729478047470407 / 5000000000000000 : ℝ)) =
              (5595326155442707 / 21458956094940814 : ℝ)
            by
        norm_num];
        exact hau452)
  have hat1 :
    (Real.pi / 2 - (2 * (510132446778923655351 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5595326155442707 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5595326155442707 : ℝ) =
              (5595326155442707 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau451)
  have hz1 :
    (10000000000000000 / 5595326155442707 : ℝ) ≤
      1 / Real.sqrt (200369118629 / 640000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5595326155442707 : ℝ) =
          1 / (5595326155442707 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 349707884715169 : ℝ) ≤
      (1332462268344726654813 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (200369118629 / 640000000000 : ℝ) ≤
      (46875000000000 / 349707884715169 : ℝ) := by
    rw [show
        (46875000000000 / 349707884715169 : ℝ) =
          (3 / 40) / (349707884715169 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (510132446778923655351 / 2000000000000000000000 : ℝ))) -
        6 * (1332462268344726654813 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (200369118629 / 640000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (200369118629 / 640000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((349707884715169 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (510132446778923655351 / 2000000000000000000000 : ℝ))) -
          6 * (1332462268344726654813 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (200369118629 / 640000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (200369118629 / 640000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (200369118629 / 640000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_341 :
    ((548443120772471356537 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2271810820302100756551 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5616994160776461 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2558905467817166652031 / 10000000000000000000000 : ℝ))) -
              6 * (265476493422338033503 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (10096199488703 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10096199488703 / 32000000000000 : ℝ)) =
      Real.log (42096199488703 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10096199488703 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10276199488703 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (548443120772471356537 / 2000000000000000000000 : ℝ) ≤
      Real.log (42096199488703 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10276199488703 / 32000000000000 : ℝ) ≤
      (-(2271810820302100756551 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (10276199488703 / 32000000000000 : ℝ) = (10276199488703 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10276199488703 / 8000000000000 : ℝ) ≤
            (500777900897899243449 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5616994160776461 / 10000000000000000 : ℝ) ≤
      Real.sqrt (10096199488703 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10096199488703 / 32000000000000 : ℝ) ≤ (351062135048529 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10096199488703 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau454 :
    Real.arctan (1872331386925488 / 7156517338005019 : ℝ) ≤
      (2558905467817166652031 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau453 :
    Real.arctan (351062135048529 / 625000000000000 : ℝ) ≤
      (2 * (2558905467817166652031 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11469552014015057 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (351062135048529 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (351062135048529 / 625000000000000 : ℝ) /
                (1 + (11469552014015057 / 10000000000000000 : ℝ)) =
              (1872331386925488 / 7156517338005019 : ℝ)
            by
        norm_num];
        exact hau454)
  have hat1 :
    (Real.pi / 2 - (2 * (2558905467817166652031 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 351062135048529 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 351062135048529 : ℝ) =
              (351062135048529 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau453)
  have hz1 :
    (625000000000000 / 351062135048529 : ℝ) ≤
      1 / Real.sqrt (10096199488703 / 32000000000000 : ℝ) := by
    rw [show (625000000000000 / 351062135048529 : ℝ) = 1 / (351062135048529 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1872331386925487 : ℝ) ≤
      (265476493422338033503 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10096199488703 / 32000000000000 : ℝ) ≤
      (250000000000000 / 1872331386925487 : ℝ) := by
    rw [show
        (250000000000000 / 1872331386925487 : ℝ) =
          (3 / 40) / (5616994160776461 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2558905467817166652031 / 10000000000000000000000 : ℝ))) -
        6 * (265476493422338033503 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10096199488703 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10096199488703 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5616994160776461 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2558905467817166652031 / 10000000000000000000000 : ℝ))) -
          6 * (265476493422338033503 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (10096199488703 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10096199488703 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10096199488703 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_342 :
    ((1380333320836278337613 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5641842422477859503957 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5638578900628463 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (40110966774065083747 / 156250000000000000000 : ℝ))) -
              6 * (1322360325788739087959 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2543485761489 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2543485761489 / 8000000000000 : ℝ)) =
      Real.log (10543485761489 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2543485761489 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2588485761489 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1380333320836278337613 / 5000000000000000000000 : ℝ) ≤
      Real.log (10543485761489 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2588485761489 / 8000000000000 : ℝ) ≤
      (-(5641842422477859503957 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2588485761489 / 8000000000000 : ℝ) = (2588485761489 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2588485761489 / 2000000000000 : ℝ) ≤
            (1289629380522140496043 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5638578900628463 / 10000000000000000 : ℝ) ≤ Real.sqrt (2543485761489 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2543485761489 / 8000000000000 : ℝ) ≤ (2819289450314233 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2543485761489 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau456 :
    Real.arctan (5638578900628466 / 21480138153289467 : ℝ) ≤
      (40110966774065083747 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau455 :
    Real.arctan (2819289450314233 / 5000000000000000 : ℝ) ≤
      (2 * (40110966774065083747 / 156250000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11480138153289467 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2819289450314233 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2819289450314233 / 5000000000000000 : ℝ) /
                (1 + (11480138153289467 / 10000000000000000 : ℝ)) =
              (5638578900628466 / 21480138153289467 : ℝ)
            by
        norm_num];
        exact hau456)
  have hat1 :
    (Real.pi / 2 - (2 * (40110966774065083747 / 156250000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2819289450314233 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2819289450314233 : ℝ) =
              (2819289450314233 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau455)
  have hz1 :
    (5000000000000000 / 2819289450314233 : ℝ) ≤
      1 / Real.sqrt (2543485761489 / 8000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2819289450314233 : ℝ) = 1 / (2819289450314233 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5638578900628463 : ℝ) ≤
      (1322360325788739087959 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2543485761489 / 8000000000000 : ℝ) ≤
      (750000000000000 / 5638578900628463 : ℝ) := by
    rw [show
        (750000000000000 / 5638578900628463 : ℝ) =
          (3 / 40) / (5638578900628463 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (40110966774065083747 / 156250000000000000000 : ℝ))) -
        6 * (1322360325788739087959 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2543485761489 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2543485761489 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5638578900628463 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (40110966774065083747 / 156250000000000000000 : ℝ))) -
          6 * (1322360325788739087959 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2543485761489 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2543485761489 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2543485761489 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_343 :
    ((2779083698092697689807 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2241775878834215454377 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1415020331899601 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1287625992309098770811 / 5000000000000000000000 : ℝ))) -
              6 * (1317394761724191804781 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10251686603209 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10251686603209 / 32000000000000 : ℝ)) =
      Real.log (42251686603209 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10251686603209 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10431686603209 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2779083698092697689807 / 10000000000000000000000 : ℝ) ≤
      Real.log (42251686603209 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10431686603209 / 32000000000000 : ℝ) ≤
      (-(2241775878834215454377 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (10431686603209 / 32000000000000 : ℝ) = (10431686603209 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10431686603209 / 8000000000000 : ℝ) ≤
            (530812842365784545623 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1415020331899601 / 2500000000000000 : ℝ) ≤ Real.sqrt (10251686603209 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10251686603209 / 32000000000000 : ℝ) ≤
      (5660081327598407 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10251686603209 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau458 :
    Real.arctan (5660081327598407 / 21490714539793777 : ℝ) ≤
      (1287625992309098770811 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau457 :
    Real.arctan (5660081327598407 / 10000000000000000 : ℝ) ≤
      (2 * (1287625992309098770811 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11490714539793777 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5660081327598407 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5660081327598407 / 10000000000000000 : ℝ) /
                (1 + (11490714539793777 / 10000000000000000 : ℝ)) =
              (5660081327598407 / 21490714539793777 : ℝ)
            by
        norm_num];
        exact hau458)
  have hat1 :
    (Real.pi / 2 - (2 * (1287625992309098770811 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5660081327598407 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5660081327598407 : ℝ) =
              (5660081327598407 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau457)
  have hz1 :
    (10000000000000000 / 5660081327598407 : ℝ) ≤
      1 / Real.sqrt (10251686603209 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5660081327598407 : ℝ) =
          1 / (5660081327598407 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1415020331899601 : ℝ) ≤
      (1317394761724191804781 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10251686603209 / 32000000000000 : ℝ) ≤
      (187500000000000 / 1415020331899601 : ℝ) := by
    rw [show
        (187500000000000 / 1415020331899601 : ℝ) =
          (3 / 40) / (1415020331899601 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1287625992309098770811 / 5000000000000000000000 : ℝ))) -
        6 * (1317394761724191804781 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10251686603209 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10251686603209 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1415020331899601 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1287625992309098770811 / 5000000000000000000000 : ℝ))) -
          6 * (1317394761724191804781 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10251686603209 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10251686603209 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10251686603209 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_344 :
    ((1398733449030094056213 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2783657344140277014661 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2840751188129811 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (322919540605409180593 / 1250000000000000000000 : ℝ))) -
              6 * (131248472051481762243 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (5164715080231 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5164715080231 / 16000000000000 : ℝ)) =
      Real.log (21164715080231 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5164715080231 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5254715080231 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1398733449030094056213 / 5000000000000000000000 : ℝ) ≤
      Real.log (21164715080231 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5254715080231 / 16000000000000 : ℝ) ≤
      (-(2783657344140277014661 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (5254715080231 / 16000000000000 : ℝ) = (5254715080231 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5254715080231 / 4000000000000 : ℝ) ≤
            (682078557359722985339 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2840751188129811 / 5000000000000000 : ℝ) ≤ Real.sqrt (5164715080231 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5164715080231 / 16000000000000 : ℝ) ≤ (45452019010077 / 80000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5164715080231 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau460 :
    Real.arctan (5681502376259625 / 21501281200433443 : ℝ) ≤
      (322919540605409180593 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau459 :
    Real.arctan (45452019010077 / 80000000000000 : ℝ) ≤
      (2 * (322919540605409180593 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11501281200433443 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (45452019010077 / 80000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (45452019010077 / 80000000000000 : ℝ) /
                (1 + (11501281200433443 / 10000000000000000 : ℝ)) =
              (5681502376259625 / 21501281200433443 : ℝ)
            by
        norm_num];
        exact hau460)
  have hat1 :
    (Real.pi / 2 - (2 * (322919540605409180593 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (80000000000000 / 45452019010077 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (80000000000000 / 45452019010077 : ℝ) =
              (45452019010077 / 80000000000000 : ℝ)
            by
        norm_num];
        exact hau459)
  have hz1 :
    (80000000000000 / 45452019010077 : ℝ) ≤ 1 / Real.sqrt (5164715080231 / 16000000000000 : ℝ) := by
    rw [show (80000000000000 / 45452019010077 : ℝ) = 1 / (45452019010077 / 80000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 946917062709937 : ℝ) ≤
      (131248472051481762243 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5164715080231 / 16000000000000 : ℝ) ≤
      (125000000000000 / 946917062709937 : ℝ) := by
    rw [show
        (125000000000000 / 946917062709937 : ℝ) =
          (3 / 40) / (2840751188129811 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (322919540605409180593 / 1250000000000000000000 : ℝ))) -
        6 * (131248472051481762243 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5164715080231 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5164715080231 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2840751188129811 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (322919540605409180593 / 1250000000000000000000 : ℝ))) -
          6 * (131248472051481762243 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (5164715080231 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5164715080231 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5164715080231 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_345 :
    ((2834132224953083779733 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5493881535351685480757 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1431025997411363 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (40616089696646176937 / 156250000000000000000 : ℝ))) -
              6 * (1302827124684973012057 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1310614659371 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1310614659371 / 4000000000000 : ℝ)) =
      Real.log (5310614659371 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1310614659371 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1333114659371 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2834132224953083779733 / 10000000000000000000000 : ℝ) ≤
      Real.log (5310614659371 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1333114659371 / 4000000000000 : ℝ) ≤
      (-(5493881535351685480757 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1333114659371 / 4000000000000 : ℝ) = (1333114659371 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1333114659371 / 1000000000000 : ℝ) ≤
            (1437590267648314519243 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1431025997411363 / 2500000000000000 : ℝ) ≤ Real.sqrt (1310614659371 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1310614659371 / 4000000000000 : ℝ) ≤ (1144820797929091 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1310614659371 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau462 :
    Real.arctan (5724103989645455 / 21522385451124041 : ℝ) ≤
      (40616089696646176937 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau461 :
    Real.arctan (1144820797929091 / 2000000000000000 : ℝ) ≤
      (2 * (40616089696646176937 / 156250000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11522385451124041 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1144820797929091 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1144820797929091 / 2000000000000000 : ℝ) /
                (1 + (11522385451124041 / 10000000000000000 : ℝ)) =
              (5724103989645455 / 21522385451124041 : ℝ)
            by
        norm_num];
        exact hau462)
  have hat1 :
    (Real.pi / 2 - (2 * (40616089696646176937 / 156250000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1144820797929091 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1144820797929091 : ℝ) =
              (1144820797929091 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau461)
  have hz1 :
    (2000000000000000 / 1144820797929091 : ℝ) ≤
      1 / Real.sqrt (1310614659371 / 4000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1144820797929091 : ℝ) = 1 / (1144820797929091 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1431025997411363 : ℝ) ≤
      (1302827124684973012057 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1310614659371 / 4000000000000 : ℝ) ≤
      (187500000000000 / 1431025997411363 : ℝ) := by
    rw [show
        (187500000000000 / 1431025997411363 : ℝ) =
          (3 / 40) / (1431025997411363 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (40616089696646176937 / 156250000000000000000 : ℝ))) -
        6 * (1302827124684973012057 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1310614659371 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1310614659371 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1431025997411363 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (40616089696646176937 / 156250000000000000000 : ℝ))) -
          6 * (1302827124684973012057 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1310614659371 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1310614659371 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1310614659371 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_346 :
    ((2870663608185664775589 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2710755638254187861199 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5766390874464393 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2615326125171193657161 / 10000000000000000000000 : ℝ))) -
              6 * (1293379633233145650797 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5320202194737 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5320202194737 / 16000000000000 : ℝ)) =
      Real.log (21320202194737 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5320202194737 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5410202194737 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2870663608185664775589 / 10000000000000000000000 : ℝ) ≤
      Real.log (21320202194737 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5410202194737 / 16000000000000 : ℝ) ≤
      (-(2710755638254187861199 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (5410202194737 / 16000000000000 : ℝ) = (5410202194737 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5410202194737 / 4000000000000 : ℝ) ≤
            (754980263245812138801 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5766390874464393 / 10000000000000000 : ℝ) ≤ Real.sqrt (5320202194737 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5320202194737 / 16000000000000 : ℝ) ≤ (1441597718616099 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5320202194737 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau464 :
    Real.arctan (5766390874464396 / 21543451118149469 : ℝ) ≤
      (2615326125171193657161 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau463 :
    Real.arctan (1441597718616099 / 2500000000000000 : ℝ) ≤
      (2 * (2615326125171193657161 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11543451118149469 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1441597718616099 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1441597718616099 / 2500000000000000 : ℝ) /
                (1 + (11543451118149469 / 10000000000000000 : ℝ)) =
              (5766390874464396 / 21543451118149469 : ℝ)
            by
        norm_num];
        exact hau464)
  have hat1 :
    (Real.pi / 2 - (2 * (2615326125171193657161 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1441597718616099 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1441597718616099 : ℝ) =
              (1441597718616099 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau463)
  have hz1 :
    (2500000000000000 / 1441597718616099 : ℝ) ≤
      1 / Real.sqrt (5320202194737 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1441597718616099 : ℝ) = 1 / (1441597718616099 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1922130291488131 : ℝ) ≤
      (1293379633233145650797 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5320202194737 / 16000000000000 : ℝ) ≤
      (250000000000000 / 1922130291488131 : ℝ) := by
    rw [show
        (250000000000000 / 1922130291488131 : ℝ) =
          (3 / 40) / (5766390874464393 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2615326125171193657161 / 10000000000000000000000 : ℝ))) -
        6 * (1293379633233145650797 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5320202194737 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5320202194737 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5766390874464393 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2615326125171193657161 / 10000000000000000000000 : ℝ))) -
          6 * (1293379633233145650797 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5320202194737 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5320202194737 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5320202194737 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_347 :
    ((726765505706868317119 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5350173580933170941977 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((580836990470971 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2631049342012675989687 / 10000000000000000000000 : ℝ))) -
              6 * (128413473666420098043 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (539794575199 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (539794575199 / 1600000000000 : ℝ)) =
      Real.log (2139794575199 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((539794575199 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (548794575199 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (726765505706868317119 / 2500000000000000000000 : ℝ) ≤
      Real.log (2139794575199 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (548794575199 / 1600000000000 : ℝ) ≤
      (-(5350173580933170941977 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (548794575199 / 1600000000000 : ℝ) = (548794575199 / 400000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (548794575199 / 400000000000 : ℝ) ≤
            (1581298222066829058023 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (580836990470971 / 1000000000000000 : ℝ) ≤ Real.sqrt (539794575199 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (539794575199 / 1600000000000 : ℝ) ≤ (5808369904709713 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (539794575199 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau466 :
    Real.arctan (5808369904709713 / 21564478412359871 : ℝ) ≤
      (2631049342012675989687 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau465 :
    Real.arctan (5808369904709713 / 10000000000000000 : ℝ) ≤
      (2 * (2631049342012675989687 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11564478412359871 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5808369904709713 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5808369904709713 / 10000000000000000 : ℝ) /
                (1 + (11564478412359871 / 10000000000000000 : ℝ)) =
              (5808369904709713 / 21564478412359871 : ℝ)
            by
        norm_num];
        exact hau466)
  have hat1 :
    (Real.pi / 2 - (2 * (2631049342012675989687 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5808369904709713 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5808369904709713 : ℝ) =
              (5808369904709713 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau465)
  have hz1 :
    (10000000000000000 / 5808369904709713 : ℝ) ≤
      1 / Real.sqrt (539794575199 / 1600000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5808369904709713 : ℝ) =
          1 / (5808369904709713 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 580836990470971 : ℝ) ≤
      (128413473666420098043 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (539794575199 / 1600000000000 : ℝ) ≤
      (75000000000000 / 580836990470971 : ℝ) := by
    rw [show
        (75000000000000 / 580836990470971 : ℝ) =
          (3 / 40) / (580836990470971 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2631049342012675989687 / 10000000000000000000000 : ℝ))) -
        6 * (128413473666420098043 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (539794575199 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (539794575199 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((580836990470971 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2631049342012675989687 / 10000000000000000000000 : ℝ))) -
          6 * (128413473666420098043 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (539794575199 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (539794575199 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (539794575199 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_348 :
    ((1471664216669667297137 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10559678795699479359667 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5850047707734419 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2646603120442483009779 / 10000000000000000000000 : ℝ))) -
              6 * (637542647980929447969 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (5475689309243 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5475689309243 / 16000000000000 : ℝ)) =
      Real.log (21475689309243 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5475689309243 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5565689309243 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1471664216669667297137 / 5000000000000000000000 : ℝ) ≤
      Real.log (21475689309243 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5565689309243 / 16000000000000 : ℝ) ≤
      (-(10559678795699479359667 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (5565689309243 / 16000000000000 : ℝ) = (5565689309243 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5565689309243 / 4000000000000 : ℝ) ≤
            (3303264810300520640333 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5850047707734419 / 10000000000000000 : ℝ) ≤ Real.sqrt (5475689309243 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5475689309243 / 16000000000000 : ℝ) ≤ (2925023853867211 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5475689309243 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau468 :
    Real.arctan (5850047707734422 / 21585467542691953 : ℝ) ≤
      (2646603120442483009779 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau467 :
    Real.arctan (2925023853867211 / 5000000000000000 : ℝ) ≤
      (2 * (2646603120442483009779 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11585467542691953 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2925023853867211 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2925023853867211 / 5000000000000000 : ℝ) /
                (1 + (11585467542691953 / 10000000000000000 : ℝ)) =
              (5850047707734422 / 21585467542691953 : ℝ)
            by
        norm_num];
        exact hau468)
  have hat1 :
    (Real.pi / 2 - (2 * (2646603120442483009779 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2925023853867211 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2925023853867211 : ℝ) =
              (2925023853867211 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau467)
  have hz1 :
    (5000000000000000 / 2925023853867211 : ℝ) ≤
      1 / Real.sqrt (5475689309243 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2925023853867211 : ℝ) = 1 / (2925023853867211 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5850047707734419 : ℝ) ≤
      (637542647980929447969 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5475689309243 / 16000000000000 : ℝ) ≤
      (750000000000000 / 5850047707734419 : ℝ) := by
    rw [show
        (750000000000000 / 5850047707734419 : ℝ) =
          (3 / 40) / (5850047707734419 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2646603120442483009779 / 10000000000000000000000 : ℝ))) -
        6 * (637542647980929447969 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5475689309243 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5475689309243 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5850047707734419 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2646603120442483009779 / 10000000000000000000000 : ℝ))) -
          6 * (637542647980929447969 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (5475689309243 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5475689309243 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5475689309243 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
