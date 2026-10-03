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

/-! # V18: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_217 :
    ((301168224368862296271 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17829697167130139861507 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4031291139396187 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3832009751163251614927 / 10000000000000000000000 : ℝ)) -
              6 * (919708107235846697917 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (4160334912147 / 25600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4160334912147 / 25600000000000 : ℝ)) =
      Real.log (29760334912147 / 25600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4160334912147 / 25600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4304334912147 / 25600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (301168224368862296271 / 2000000000000000000000 : ℝ) ≤
      Real.log (29760334912147 / 25600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4304334912147 / 25600000000000 : ℝ) ≤
      (-(17829697167130139861507 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4304334912147 / 25600000000000 : ℝ) = (4304334912147 / 3200000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4304334912147 / 3200000000000 : ℝ) ≤
            (2964718241869860138493 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4031291139396187 / 10000000000000000 : ℝ) ≤ Real.sqrt (4160334912147 / 25600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4160334912147 / 25600000000000 : ℝ) ≤ (403129113939619 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4160334912147 / 25600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau279 :
    Real.arctan (403129113939619 / 1000000000000000 : ℝ) ≤
      (3832009751163251614927 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3832009751163251614927 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 403129113939619 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 403129113939619 : ℝ) =
              (403129113939619 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau279)
  have hz1 :
    (1000000000000000 / 403129113939619 : ℝ) ≤
      1 / Real.sqrt (4160334912147 / 25600000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 403129113939619 : ℝ) = 1 / (403129113939619 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4031291139396187 : ℝ) ≤
      (919708107235846697917 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4160334912147 / 25600000000000 : ℝ) ≤
      (750000000000000 / 4031291139396187 : ℝ) := by
    rw [show
        (750000000000000 / 4031291139396187 : ℝ) =
          (3 / 40) / (4031291139396187 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3832009751163251614927 / 10000000000000000000000 : ℝ)) -
        6 * (919708107235846697917 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4160334912147 / 25600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4160334912147 / 25600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4031291139396187 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3832009751163251614927 / 10000000000000000000000 : ℝ)) -
          6 * (919708107235846697917 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (4160334912147 / 25600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4160334912147 / 25600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4160334912147 / 25600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_218 :
    ((11794189169129279047 / 78125000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4450837296658632106129 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2018394637647063 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1918369187644382154269 / 5000000000000000000000 : ℝ)) -
              6 * (1836966934064261994179 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10429227298003 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10429227298003 / 64000000000000 : ℝ)) =
      Real.log (74429227298003 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10429227298003 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10789227298003 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (11794189169129279047 / 78125000000000000000 : ℝ) ≤
      Real.log (74429227298003 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10789227298003 / 64000000000000 : ℝ) ≤
      (-(4450837296658632106129 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (10789227298003 / 64000000000000 : ℝ) = (10789227298003 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10789227298003 / 8000000000000 : ℝ) ≤
            (747766555591367893871 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2018394637647063 / 5000000000000000 : ℝ) ≤ Real.sqrt (10429227298003 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10429227298003 / 64000000000000 : ℝ) ≤
      (4036789275294129 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10429227298003 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau280 :
    Real.arctan (4036789275294129 / 10000000000000000 : ℝ) ≤
      (1918369187644382154269 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1918369187644382154269 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4036789275294129 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4036789275294129 : ℝ) =
              (4036789275294129 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau280)
  have hz1 :
    (10000000000000000 / 4036789275294129 : ℝ) ≤
      1 / Real.sqrt (10429227298003 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4036789275294129 : ℝ) =
          1 / (4036789275294129 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 672798212549021 : ℝ) ≤
      (1836966934064261994179 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10429227298003 / 64000000000000 : ℝ) ≤
      (125000000000000 / 672798212549021 : ℝ) := by
    rw [show
        (125000000000000 / 672798212549021 : ℝ) =
          (3 / 40) / (2018394637647063 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1918369187644382154269 / 5000000000000000000000 : ℝ)) -
        6 * (1836966934064261994179 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10429227298003 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10429227298003 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2018394637647063 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1918369187644382154269 / 5000000000000000000000 : ℝ)) -
          6 * (1836966934064261994179 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10429227298003 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10429227298003 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10429227298003 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_219 :
    ((189183731314411355741 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1777707044535513541937 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1010569983217551 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (480182345859374426031 / 1250000000000000000000 : ℝ)) -
              6 * (229315926589210924701 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (20915234631277 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20915234631277 / 128000000000000 : ℝ)) =
      Real.log (148915234631277 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20915234631277 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21635234631277 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (189183731314411355741 / 1250000000000000000000 : ℝ) ≤
      Real.log (148915234631277 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21635234631277 / 128000000000000 : ℝ) ≤
      (-(1777707044535513541937 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21635234631277 / 128000000000000 : ℝ) = (21635234631277 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21635234631277 / 16000000000000 : ℝ) ≤
            (301734496364486458063 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1010569983217551 / 2500000000000000 : ℝ) ≤
      Real.sqrt (20915234631277 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20915234631277 / 128000000000000 : ℝ) ≤
      (4042279932870207 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20915234631277 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau281 :
    Real.arctan (4042279932870207 / 10000000000000000 : ℝ) ≤
      (480182345859374426031 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (480182345859374426031 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4042279932870207 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4042279932870207 : ℝ) =
              (4042279932870207 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau281)
  have hz1 :
    (10000000000000000 / 4042279932870207 : ℝ) ≤
      1 / Real.sqrt (20915234631277 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4042279932870207 : ℝ) =
          1 / (4042279932870207 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 336856661072517 : ℝ) ≤
      (229315926589210924701 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20915234631277 / 128000000000000 : ℝ) ≤
      (62500000000000 / 336856661072517 : ℝ) := by
    rw [show
        (62500000000000 / 336856661072517 : ℝ) =
          (3 / 40) / (1010569983217551 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (480182345859374426031 / 1250000000000000000000 : ℝ)) -
        6 * (229315926589210924701 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20915234631277 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20915234631277 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1010569983217551 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (480182345859374426031 / 1250000000000000000000 : ℝ)) -
          6 * (229315926589210924701 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (20915234631277 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20915234631277 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20915234631277 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_220 :
    ((1517282033553838498547 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17750860580341441455871 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((809552628511343 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1923085479175907476307 / 5000000000000000000000 : ℝ)) -
              6 * (458024396444353584973 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (5243003666637 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5243003666637 / 32000000000000 : ℝ)) =
      Real.log (37243003666637 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5243003666637 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5423003666637 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1517282033553838498547 / 10000000000000000000000 : ℝ) ≤
      Real.log (37243003666637 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5423003666637 / 32000000000000 : ℝ) ≤
      (-(17750860580341441455871 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5423003666637 / 32000000000000 : ℝ) = (5423003666637 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5423003666637 / 4000000000000 : ℝ) ≤
            (3043554828658558544129 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (809552628511343 / 2000000000000000 : ℝ) ≤ Real.sqrt (5243003666637 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5243003666637 / 32000000000000 : ℝ) ≤ (2023881571278359 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5243003666637 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau282 :
    Real.arctan (2023881571278359 / 5000000000000000 : ℝ) ≤
      (1923085479175907476307 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1923085479175907476307 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2023881571278359 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2023881571278359 : ℝ) =
              (2023881571278359 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau282)
  have hz1 :
    (5000000000000000 / 2023881571278359 : ℝ) ≤
      1 / Real.sqrt (5243003666637 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2023881571278359 : ℝ) = 1 / (2023881571278359 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 809552628511343 : ℝ) ≤
      (458024396444353584973 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5243003666637 / 32000000000000 : ℝ) ≤
      (150000000000000 / 809552628511343 : ℝ) := by
    rw [show
        (150000000000000 / 809552628511343 : ℝ) =
          (3 / 40) / (809552628511343 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1923085479175907476307 / 5000000000000000000000 : ℝ)) -
        6 * (458024396444353584973 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5243003666637 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5243003666637 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((809552628511343 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1923085479175907476307 / 5000000000000000000000 : ℝ)) -
          6 * (458024396444353584973 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (5243003666637 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5243003666637 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5243003666637 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_221 :
    ((1521092763872220139037 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17724719231489336947553 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4053238934580107 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3850874981935184802889 / 10000000000000000000000 : ℝ)) -
              6 * (182967738921082186107 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (21028794701819 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21028794701819 / 128000000000000 : ℝ)) =
      Real.log (149028794701819 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21028794701819 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21748794701819 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1521092763872220139037 / 10000000000000000000000 : ℝ) ≤
      Real.log (149028794701819 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21748794701819 / 128000000000000 : ℝ) ≤
      (-(17724719231489336947553 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21748794701819 / 128000000000000 : ℝ) = (21748794701819 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21748794701819 / 16000000000000 : ℝ) ≤
            (3069696177510663052447 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4053238934580107 / 10000000000000000 : ℝ) ≤
      Real.sqrt (21028794701819 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21028794701819 / 128000000000000 : ℝ) ≤ (405323893458011 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21028794701819 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau283 :
    Real.arctan (405323893458011 / 1000000000000000 : ℝ) ≤
      (3850874981935184802889 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3850874981935184802889 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 405323893458011 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 405323893458011 : ℝ) =
              (405323893458011 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau283)
  have hz1 :
    (1000000000000000 / 405323893458011 : ℝ) ≤
      1 / Real.sqrt (21028794701819 / 128000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 405323893458011 : ℝ) = 1 / (405323893458011 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4053238934580107 : ℝ) ≤
      (182967738921082186107 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21028794701819 / 128000000000000 : ℝ) ≤
      (750000000000000 / 4053238934580107 : ℝ) := by
    rw [show
        (750000000000000 / 4053238934580107 : ℝ) =
          (3 / 40) / (4053238934580107 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3850874981935184802889 / 10000000000000000000000 : ℝ)) -
        6 * (182967738921082186107 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21028794701819 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21028794701819 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4053238934580107 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3850874981935184802889 / 10000000000000000000000 : ℝ)) -
          6 * (182967738921082186107 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (21028794701819 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21028794701819 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21028794701819 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_222 :
    ((1524902042577198992607 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2212330755188929494453 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((405870733896293 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3855570869629157385863 / 10000000000000000000000 : ℝ)) -
              6 * (228408344945016066593 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (2108557473709 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2108557473709 / 12800000000000 : ℝ)) =
      Real.log (14908557473709 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2108557473709 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2180557473709 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1524902042577198992607 / 10000000000000000000000 : ℝ) ≤
      Real.log (14908557473709 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2180557473709 / 12800000000000 : ℝ) ≤
      (-(2212330755188929494453 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2180557473709 / 12800000000000 : ℝ) = (2180557473709 / 1600000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2180557473709 / 1600000000000 : ℝ) ≤
            (386971170936070505547 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (405870733896293 / 1000000000000000 : ℝ) ≤ Real.sqrt (2108557473709 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2108557473709 / 12800000000000 : ℝ) ≤ (4058707338962933 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2108557473709 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau284 :
    Real.arctan (4058707338962933 / 10000000000000000 : ℝ) ≤
      (3855570869629157385863 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3855570869629157385863 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4058707338962933 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4058707338962933 : ℝ) =
              (4058707338962933 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau284)
  have hz1 :
    (10000000000000000 / 4058707338962933 : ℝ) ≤
      1 / Real.sqrt (2108557473709 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4058707338962933 : ℝ) =
          1 / (4058707338962933 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 405870733896293 : ℝ) ≤
      (228408344945016066593 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2108557473709 / 12800000000000 : ℝ) ≤
      (75000000000000 / 405870733896293 : ℝ) := by
    rw [show
        (75000000000000 / 405870733896293 : ℝ) =
          (3 / 40) / (405870733896293 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3855570869629157385863 / 10000000000000000000000 : ℝ)) -
        6 * (228408344945016066593 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2108557473709 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2108557473709 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((405870733896293 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3855570869629157385863 / 10000000000000000000000 : ℝ)) -
          6 * (228408344945016066593 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (2108557473709 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2108557473709 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2108557473709 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_223 :
    ((1528709870774273975149 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17672640655907776151439 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((812833677105151 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3860258653227845737129 / 10000000000000000000000 : ℝ)) -
              6 * (912432816977701343561 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (21142354772361 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21142354772361 / 128000000000000 : ℝ)) =
      Real.log (149142354772361 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21142354772361 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21862354772361 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1528709870774273975149 / 10000000000000000000000 : ℝ) ≤
      Real.log (149142354772361 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21862354772361 / 128000000000000 : ℝ) ≤
      (-(17672640655907776151439 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21862354772361 / 128000000000000 : ℝ) = (21862354772361 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21862354772361 / 16000000000000 : ℝ) ≤
            (3121774753092223848561 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (812833677105151 / 2000000000000000 : ℝ) ≤ Real.sqrt (21142354772361 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21142354772361 / 128000000000000 : ℝ) ≤
      (2032084192762879 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21142354772361 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau285 :
    Real.arctan (2032084192762879 / 5000000000000000 : ℝ) ≤
      (3860258653227845737129 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3860258653227845737129 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2032084192762879 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2032084192762879 : ℝ) =
              (2032084192762879 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau285)
  have hz1 :
    (5000000000000000 / 2032084192762879 : ℝ) ≤
      1 / Real.sqrt (21142354772361 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2032084192762879 : ℝ) = 1 / (2032084192762879 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 812833677105151 : ℝ) ≤
      (912432816977701343561 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21142354772361 / 128000000000000 : ℝ) ≤
      (150000000000000 / 812833677105151 : ℝ) := by
    rw [show
        (150000000000000 / 812833677105151 : ℝ) =
          (3 / 40) / (812833677105151 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3860258653227845737129 / 10000000000000000000000 : ℝ)) -
        6 * (912432816977701343561 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21142354772361 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21142354772361 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((812833677105151 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3860258653227845737129 / 10000000000000000000000 : ℝ)) -
          6 * (912432816977701343561 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (21142354772361 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21142354772361 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21142354772361 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_224 :
    ((76625812478384080911 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8823351361468449374261 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1017405525972267 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (241558647769835521489 / 625000000000000000000 : ℝ)) -
              6 * (1822473950103674257329 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1324945925477 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1324945925477 / 8000000000000 : ℝ)) =
      Real.log (9324945925477 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1324945925477 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1369945925477 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (76625812478384080911 / 500000000000000000000 : ℝ) ≤
      Real.log (9324945925477 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1369945925477 / 8000000000000 : ℝ) ≤
      (-(8823351361468449374261 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1369945925477 / 8000000000000 : ℝ) = (1369945925477 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1369945925477 / 1000000000000 : ℝ) ≤
            (1573856343031550625739 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1017405525972267 / 2500000000000000 : ℝ) ≤ Real.sqrt (1324945925477 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1324945925477 / 8000000000000 : ℝ) ≤ (4069622103889071 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1324945925477 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau286 :
    Real.arctan (4069622103889071 / 10000000000000000 : ℝ) ≤
      (241558647769835521489 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (241558647769835521489 / 625000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4069622103889071 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4069622103889071 : ℝ) =
              (4069622103889071 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau286)
  have hz1 :
    (10000000000000000 / 4069622103889071 : ℝ) ≤
      1 / Real.sqrt (1324945925477 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4069622103889071 : ℝ) =
          1 / (4069622103889071 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 339135175324089 : ℝ) ≤
      (1822473950103674257329 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1324945925477 / 8000000000000 : ℝ) ≤
      (62500000000000 / 339135175324089 : ℝ) := by
    rw [show
        (62500000000000 / 339135175324089 : ℝ) =
          (3 / 40) / (1017405525972267 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (241558647769835521489 / 625000000000000000000 : ℝ)) -
        6 * (1822473950103674257329 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1324945925477 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1324945925477 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1017405525972267 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (241558647769835521489 / 625000000000000000000 : ℝ)) -
          6 * (1822473950103674257329 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1324945925477 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1324945925477 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1324945925477 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_225 :
    ((1540124663354140614713 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17595027821549266170449 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((408050767350993 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3874273694284965512503 / 10000000000000000000000 : ℝ)) -
              6 * (1817718661331479209709 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10656347439087 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10656347439087 / 64000000000000 : ℝ)) =
      Real.log (74656347439087 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10656347439087 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11016347439087 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1540124663354140614713 / 10000000000000000000000 : ℝ) ≤
      Real.log (74656347439087 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11016347439087 / 64000000000000 : ℝ) ≤
      (-(17595027821549266170449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (11016347439087 / 64000000000000 : ℝ) = (11016347439087 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11016347439087 / 8000000000000 : ℝ) ≤
            (3199387587450733829551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (408050767350993 / 1000000000000000 : ℝ) ≤ Real.sqrt (10656347439087 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10656347439087 / 64000000000000 : ℝ) ≤
      (4080507673509933 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10656347439087 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau287 :
    Real.arctan (4080507673509933 / 10000000000000000 : ℝ) ≤
      (3874273694284965512503 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3874273694284965512503 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4080507673509933 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4080507673509933 : ℝ) =
              (4080507673509933 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau287)
  have hz1 :
    (10000000000000000 / 4080507673509933 : ℝ) ≤
      1 / Real.sqrt (10656347439087 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4080507673509933 : ℝ) =
          1 / (4080507673509933 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (25000000000000 / 136016922450331 : ℝ) ≤
      (1817718661331479209709 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10656347439087 / 64000000000000 : ℝ) ≤
      (25000000000000 / 136016922450331 : ℝ) := by
    rw [show
        (25000000000000 / 136016922450331 : ℝ) =
          (3 / 40) / (408050767350993 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3874273694284965512503 / 10000000000000000000000 : ℝ)) -
        6 * (1817718661331479209709 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10656347439087 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10656347439087 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((408050767350993 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3874273694284965512503 / 10000000000000000000000 : ℝ)) -
          6 * (1817718661331479209709 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10656347439087 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10656347439087 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10656347439087 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_226 :
    ((773863646372646733217 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17543618577511353923213 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((255710267553653 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (970894277033406227889 / 2500000000000000000000 : ℝ)) -
              6 * (453250101545841468879 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (5356563737179 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5356563737179 / 32000000000000 : ℝ)) =
      Real.log (37356563737179 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5356563737179 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5536563737179 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (773863646372646733217 / 5000000000000000000000 : ℝ) ≤
      Real.log (37356563737179 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5536563737179 / 32000000000000 : ℝ) ≤
      (-(17543618577511353923213 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5536563737179 / 32000000000000 : ℝ) = (5536563737179 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5536563737179 / 4000000000000 : ℝ) ≤
            (3250796831488646076787 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (255710267553653 / 625000000000000 : ℝ) ≤ Real.sqrt (5356563737179 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5356563737179 / 32000000000000 : ℝ) ≤ (4091364280858451 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5356563737179 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau288 :
    Real.arctan (4091364280858451 / 10000000000000000 : ℝ) ≤
      (970894277033406227889 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (970894277033406227889 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4091364280858451 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4091364280858451 : ℝ) =
              (4091364280858451 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau288)
  have hz1 :
    (10000000000000000 / 4091364280858451 : ℝ) ≤
      1 / Real.sqrt (5356563737179 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4091364280858451 : ℝ) =
          1 / (4091364280858451 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 255710267553653 : ℝ) ≤
      (453250101545841468879 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5356563737179 / 32000000000000 : ℝ) ≤
      (46875000000000 / 255710267553653 : ℝ) := by
    rw [show
        (46875000000000 / 255710267553653 : ℝ) =
          (3 / 40) / (255710267553653 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (970894277033406227889 / 2500000000000000000000 : ℝ)) -
        6 * (453250101545841468879 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5356563737179 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5356563737179 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((255710267553653 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (970894277033406227889 / 2500000000000000000000 : ℝ)) -
          6 * (453250101545841468879 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (5356563737179 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5356563737179 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5356563737179 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_227 :
    ((1555324146529782093153 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3498494454666579830101 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((256387009742743 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (973212212814486599171 / 2500000000000000000000 : ℝ)) -
              6 * (1808318706405921828007 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10769907509629 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10769907509629 / 64000000000000 : ℝ)) =
      Real.log (74769907509629 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10769907509629 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11129907509629 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1555324146529782093153 / 10000000000000000000000 : ℝ) ≤
      Real.log (74769907509629 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11129907509629 / 64000000000000 : ℝ) ≤
      (-(3498494454666579830101 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (11129907509629 / 64000000000000 : ℝ) = (11129907509629 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11129907509629 / 8000000000000 : ℝ) ≤
            (660388627133420169899 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (256387009742743 / 625000000000000 : ℝ) ≤ Real.sqrt (10769907509629 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10769907509629 / 64000000000000 : ℝ) ≤
      (4102192155883891 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10769907509629 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau289 :
    Real.arctan (4102192155883891 / 10000000000000000 : ℝ) ≤
      (973212212814486599171 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (973212212814486599171 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4102192155883891 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4102192155883891 : ℝ) =
              (4102192155883891 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau289)
  have hz1 :
    (10000000000000000 / 4102192155883891 : ℝ) ≤
      1 / Real.sqrt (10769907509629 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4102192155883891 : ℝ) =
          1 / (4102192155883891 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 256387009742743 : ℝ) ≤
      (1808318706405921828007 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10769907509629 / 64000000000000 : ℝ) ≤
      (46875000000000 / 256387009742743 : ℝ) := by
    rw [show
        (46875000000000 / 256387009742743 : ℝ) =
          (3 / 40) / (256387009742743 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (973212212814486599171 / 2500000000000000000000 : ℝ)) -
        6 * (1808318706405921828007 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10769907509629 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10769907509629 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((256387009742743 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (973212212814486599171 / 2500000000000000000000 : ℝ)) -
          6 * (1808318706405921828007 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10769907509629 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10769907509629 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10769907509629 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_228 :
    ((1562915233476233808219 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17441586233008606041231 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2056495762754341 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3902089165903819241319 / 10000000000000000000000 : ℝ)) -
              6 * (1803673092348793482377 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (108266875449 / 640000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (108266875449 / 640000000000 : ℝ)) =
      Real.log (748266875449 / 640000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((108266875449 / 640000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (111866875449 / 640000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1562915233476233808219 / 10000000000000000000000 : ℝ) ≤
      Real.log (748266875449 / 640000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (111866875449 / 640000000000 : ℝ) ≤
      (-(17441586233008606041231 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (111866875449 / 640000000000 : ℝ) = (111866875449 / 80000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (111866875449 / 80000000000 : ℝ) ≤
            (3352829175991393958769 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2056495762754341 / 5000000000000000 : ℝ) ≤ Real.sqrt (108266875449 / 640000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (108266875449 / 640000000000 : ℝ) ≤ (822598305101737 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (108266875449 / 640000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau290 :
    Real.arctan (822598305101737 / 2000000000000000 : ℝ) ≤
      (3902089165903819241319 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3902089165903819241319 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 822598305101737 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 822598305101737 : ℝ) =
              (822598305101737 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau290)
  have hz1 :
    (2000000000000000 / 822598305101737 : ℝ) ≤ 1 / Real.sqrt (108266875449 / 640000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 822598305101737 : ℝ) = 1 / (822598305101737 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2056495762754341 : ℝ) ≤
      (1803673092348793482377 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (108266875449 / 640000000000 : ℝ) ≤
      (375000000000000 / 2056495762754341 : ℝ) := by
    rw [show
        (375000000000000 / 2056495762754341 : ℝ) =
          (3 / 40) / (2056495762754341 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3902089165903819241319 / 10000000000000000000000 : ℝ)) -
        6 * (1803673092348793482377 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (108266875449 / 640000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (108266875449 / 640000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2056495762754341 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3902089165903819241319 / 10000000000000000000000 : ℝ)) -
          6 * (1803673092348793482377 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (108266875449 / 640000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (108266875449 / 640000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (108266875449 / 640000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
