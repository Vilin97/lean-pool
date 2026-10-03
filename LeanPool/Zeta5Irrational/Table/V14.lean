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

/-! # V14: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_169 :
    ((1071890317176583928039 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21305693393452711451859 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3363698176688539 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1622404481577912283161 / 5000000000000000000000 : ℝ)) -
              6 * (548450874824163752413 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (7241257871269 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7241257871269 / 64000000000000 : ℝ)) =
      Real.log (71241257871269 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7241257871269 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7601257871269 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1071890317176583928039 / 10000000000000000000000 : ℝ) ≤
      Real.log (71241257871269 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7601257871269 / 64000000000000 : ℝ) ≤
      (-(21305693393452711451859 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7601257871269 / 64000000000000 : ℝ) = (7601257871269 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7601257871269 / 4000000000000 : ℝ) ≤
            (6420193818547288548141 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3363698176688539 / 10000000000000000 : ℝ) ≤ Real.sqrt (7241257871269 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7241257871269 / 64000000000000 : ℝ) ≤ (1681849088344271 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7241257871269 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau231 :
    Real.arctan (1681849088344271 / 5000000000000000 : ℝ) ≤
      (1622404481577912283161 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1622404481577912283161 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1681849088344271 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1681849088344271 : ℝ) =
              (1681849088344271 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau231)
  have hz1 :
    (5000000000000000 / 1681849088344271 : ℝ) ≤
      1 / Real.sqrt (7241257871269 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1681849088344271 : ℝ) = 1 / (1681849088344271 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3363698176688539 : ℝ) ≤
      (548450874824163752413 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7241257871269 / 64000000000000 : ℝ) ≤
      (750000000000000 / 3363698176688539 : ℝ) := by
    rw [show
        (750000000000000 / 3363698176688539 : ℝ) =
          (3 / 40) / (3363698176688539 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1622404481577912283161 / 5000000000000000000000 : ℝ)) -
        6 * (548450874824163752413 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7241257871269 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7241257871269 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3363698176688539 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1622404481577912283161 / 5000000000000000000000 : ℝ)) -
          6 * (548450874824163752413 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (7241257871269 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7241257871269 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7241257871269 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_170 :
    ((1075037203912298076033 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10638119306132417311027 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1684450974174337 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (812370766620299188099 / 2500000000000000000000 : ℝ)) -
              6 * (273815285801581864431 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (907960027007 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (907960027007 / 8000000000000 : ℝ)) =
      Real.log (8907960027007 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((907960027007 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (952960027007 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1075037203912298076033 / 10000000000000000000000 : ℝ) ≤
      Real.log (8907960027007 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (952960027007 / 8000000000000 : ℝ) ≤
      (-(10638119306132417311027 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (952960027007 / 8000000000000 : ℝ) = (952960027007 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (952960027007 / 500000000000 : ℝ) ≤
            (3224824299867582688973 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1684450974174337 / 5000000000000000 : ℝ) ≤ Real.sqrt (907960027007 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (907960027007 / 8000000000000 : ℝ) ≤ (3368901948348677 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (907960027007 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau232 :
    Real.arctan (3368901948348677 / 10000000000000000 : ℝ) ≤
      (812370766620299188099 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (812370766620299188099 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3368901948348677 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3368901948348677 : ℝ) =
              (3368901948348677 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau232)
  have hz1 :
    (10000000000000000 / 3368901948348677 : ℝ) ≤
      1 / Real.sqrt (907960027007 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3368901948348677 : ℝ) =
          1 / (3368901948348677 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1684450974174337 : ℝ) ≤
      (273815285801581864431 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (907960027007 / 8000000000000 : ℝ) ≤
      (375000000000000 / 1684450974174337 : ℝ) := by
    rw [show
        (375000000000000 / 1684450974174337 : ℝ) =
          (3 / 40) / (1684450974174337 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (812370766620299188099 / 2500000000000000000000 : ℝ)) -
        6 * (273815285801581864431 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (907960027007 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (907960027007 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1684450974174337 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (812370766620299188099 / 2500000000000000000000 : ℝ)) -
          6 * (273815285801581864431 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (907960027007 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (907960027007 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (907960027007 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_171 :
    ((539091550334963103107 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5311717583689524422171 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((105440552949823 / 312500000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (406768561615688575177 / 1250000000000000000000 : ℝ)) -
              6 * (1093627877775185649047 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (7286102560843 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7286102560843 / 64000000000000 : ℝ)) =
      Real.log (71286102560843 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7286102560843 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7646102560843 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (539091550334963103107 / 5000000000000000000000 : ℝ) ≤
      Real.log (71286102560843 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7646102560843 / 64000000000000 : ℝ) ≤
      (-(5311717583689524422171 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7646102560843 / 64000000000000 : ℝ) = (7646102560843 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7646102560843 / 4000000000000 : ℝ) ≤
            (1619754219310475577829 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (105440552949823 / 312500000000000 : ℝ) ≤ Real.sqrt (7286102560843 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7286102560843 / 64000000000000 : ℝ) ≤ (3374097694394339 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7286102560843 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau233 :
    Real.arctan (3374097694394339 / 10000000000000000 : ℝ) ≤
      (406768561615688575177 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (406768561615688575177 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3374097694394339 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3374097694394339 : ℝ) =
              (3374097694394339 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau233)
  have hz1 :
    (10000000000000000 / 3374097694394339 : ℝ) ≤
      1 / Real.sqrt (7286102560843 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3374097694394339 : ℝ) =
          1 / (3374097694394339 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (23437500000000 / 105440552949823 : ℝ) ≤
      (1093627877775185649047 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7286102560843 / 64000000000000 : ℝ) ≤
      (23437500000000 / 105440552949823 : ℝ) := by
    rw [show
        (23437500000000 / 105440552949823 : ℝ) =
          (3 / 40) / (105440552949823 / 312500000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (406768561615688575177 / 1250000000000000000000 : ℝ)) -
        6 * (1093627877775185649047 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7286102560843 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7286102560843 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((105440552949823 / 312500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (406768561615688575177 / 1250000000000000000000 : ℝ)) -
          6 * (1093627877775185649047 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (7286102560843 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7286102560843 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7286102560843 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_172 :
    ((1081328008072146210999 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21217588054326763577179 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3379285451844349 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1629402640588147556519 / 5000000000000000000000 : ℝ)) -
              6 * (2184003797519659522247 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (730852490563 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (730852490563 / 6400000000000 : ℝ)) =
      Real.log (7130852490563 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((730852490563 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (766852490563 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1081328008072146210999 / 10000000000000000000000 : ℝ) ≤
      Real.log (7130852490563 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (766852490563 / 6400000000000 : ℝ) ≤
      (-(21217588054326763577179 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (766852490563 / 6400000000000 : ℝ) = (766852490563 / 400000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (766852490563 / 400000000000 : ℝ) ≤
            (6508299157673236422821 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3379285451844349 / 10000000000000000 : ℝ) ≤ Real.sqrt (730852490563 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (730852490563 / 6400000000000 : ℝ) ≤ (13200333796267 / 39062500000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (730852490563 / 6400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau234 :
    Real.arctan (13200333796267 / 39062500000000 : ℝ) ≤
      (1629402640588147556519 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1629402640588147556519 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (39062500000000 / 13200333796267 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (39062500000000 / 13200333796267 : ℝ) =
              (13200333796267 / 39062500000000 : ℝ)
            by
        norm_num];
        exact hau234)
  have hz1 :
    (39062500000000 / 13200333796267 : ℝ) ≤ 1 / Real.sqrt (730852490563 / 6400000000000 : ℝ) := by
    rw [show (39062500000000 / 13200333796267 : ℝ) = 1 / (13200333796267 / 39062500000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3379285451844349 : ℝ) ≤
      (2184003797519659522247 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (730852490563 / 6400000000000 : ℝ) ≤
      (750000000000000 / 3379285451844349 : ℝ) := by
    rw [show
        (750000000000000 / 3379285451844349 : ℝ) =
          (3 / 40) / (3379285451844349 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1629402640588147556519 / 5000000000000000000000 : ℝ)) -
        6 * (2184003797519659522247 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (730852490563 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (730852490563 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3379285451844349 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1629402640588147556519 / 5000000000000000000000 : ℝ)) -
          6 * (2184003797519659522247 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (730852490563 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (730852490563 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (730852490563 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_173 :
    ((271117981685262172049 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1059419563440124122021 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3384465257433817 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3263453469630001012291 / 10000000000000000000000 : ℝ)) -
              6 * (2180766304264109440283 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7330947250417 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7330947250417 / 64000000000000 : ℝ)) =
      Real.log (71330947250417 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7330947250417 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7690947250417 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (271117981685262172049 / 2500000000000000000000 : ℝ) ≤
      Real.log (71330947250417 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7690947250417 / 64000000000000 : ℝ) ≤
      (-(1059419563440124122021 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7690947250417 / 64000000000000 : ℝ) = (7690947250417 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7690947250417 / 4000000000000 : ℝ) ≤
            (326874797159875877979 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3384465257433817 / 10000000000000000 : ℝ) ≤ Real.sqrt (7330947250417 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7330947250417 / 64000000000000 : ℝ) ≤ (169223262871691 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7330947250417 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau235 :
    Real.arctan (169223262871691 / 500000000000000 : ℝ) ≤
      (3263453469630001012291 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3263453469630001012291 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 169223262871691 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 169223262871691 : ℝ) =
              (169223262871691 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau235)
  have hz1 :
    (500000000000000 / 169223262871691 : ℝ) ≤
      1 / Real.sqrt (7330947250417 / 64000000000000 : ℝ) := by
    rw [show (500000000000000 / 169223262871691 : ℝ) = 1 / (169223262871691 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3384465257433817 : ℝ) ≤
      (2180766304264109440283 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7330947250417 / 64000000000000 : ℝ) ≤
      (750000000000000 / 3384465257433817 : ℝ) := by
    rw [show
        (750000000000000 / 3384465257433817 : ℝ) =
          (3 / 40) / (3384465257433817 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3263453469630001012291 / 10000000000000000000000 : ℝ)) -
        6 * (2180766304264109440283 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7330947250417 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7330947250417 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3384465257433817 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3263453469630001012291 / 10000000000000000000000 : ℝ)) -
          6 * (2180766304264109440283 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7330947250417 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7330947250417 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7330947250417 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_174 :
    ((217522971459627535867 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5289819870100654850123 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1694818573808583 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3268093096395075635043 / 10000000000000000000000 : ℝ)) -
              6 * (2177543168845947543807 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1838342398801 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1838342398801 / 16000000000000 : ℝ)) =
      Real.log (17838342398801 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1838342398801 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1928342398801 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (217522971459627535867 / 2000000000000000000000 : ℝ) ≤
      Real.log (17838342398801 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1928342398801 / 16000000000000 : ℝ) ≤
      (-(5289819870100654850123 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1928342398801 / 16000000000000 : ℝ) = (1928342398801 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1928342398801 / 1000000000000 : ℝ) ≤
            (1641651932899345149877 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1694818573808583 / 5000000000000000 : ℝ) ≤ Real.sqrt (1838342398801 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1838342398801 / 16000000000000 : ℝ) ≤ (3389637147617169 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1838342398801 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau236 :
    Real.arctan (3389637147617169 / 10000000000000000 : ℝ) ≤
      (3268093096395075635043 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3268093096395075635043 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3389637147617169 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3389637147617169 : ℝ) =
              (3389637147617169 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau236)
  have hz1 :
    (10000000000000000 / 3389637147617169 : ℝ) ≤
      1 / Real.sqrt (1838342398801 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3389637147617169 : ℝ) =
          1 / (3389637147617169 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 564939524602861 : ℝ) ≤
      (2177543168845947543807 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1838342398801 / 16000000000000 : ℝ) ≤
      (125000000000000 / 564939524602861 : ℝ) := by
    rw [show
        (125000000000000 / 564939524602861 : ℝ) =
          (3 / 40) / (1694818573808583 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3268093096395075635043 / 10000000000000000000000 : ℝ)) -
        6 * (2177543168845947543807 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1838342398801 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1838342398801 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1694818573808583 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3268093096395075635043 / 10000000000000000000000 : ℝ)) -
          6 * (2177543168845947543807 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1838342398801 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1838342398801 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1838342398801 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_175 :
    ((1093897756559963010019 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2637663615683673257443 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((339995732619773 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1638673407935689605673 / 5000000000000000000000 : ℝ)) -
              6 * (2171139549275033092439 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3699107142389 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3699107142389 / 32000000000000 : ℝ)) =
      Real.log (35699107142389 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3699107142389 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3879107142389 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1093897756559963010019 / 10000000000000000000000 : ℝ) ≤
      Real.log (35699107142389 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3879107142389 / 32000000000000 : ℝ) ≤
      (-(2637663615683673257443 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3879107142389 / 32000000000000 : ℝ) = (3879107142389 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3879107142389 / 2000000000000 : ℝ) ≤
            (828072285816326742557 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (339995732619773 / 1000000000000000 : ℝ) ≤ Real.sqrt (3699107142389 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3699107142389 / 32000000000000 : ℝ) ≤ (3399957326197733 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3699107142389 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau237 :
    Real.arctan (3399957326197733 / 10000000000000000 : ℝ) ≤
      (1638673407935689605673 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1638673407935689605673 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3399957326197733 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3399957326197733 : ℝ) =
              (3399957326197733 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau237)
  have hz1 :
    (10000000000000000 / 3399957326197733 : ℝ) ≤
      1 / Real.sqrt (3699107142389 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3399957326197733 : ℝ) =
          1 / (3399957326197733 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 339995732619773 : ℝ) ≤
      (2171139549275033092439 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3699107142389 / 32000000000000 : ℝ) ≤
      (75000000000000 / 339995732619773 : ℝ) := by
    rw [show
        (75000000000000 / 339995732619773 : ℝ) =
          (3 / 40) / (339995732619773 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1638673407935689605673 / 5000000000000000000000 : ℝ)) -
        6 * (2171139549275033092439 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3699107142389 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3699107142389 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((339995732619773 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1638673407935689605673 / 5000000000000000000000 : ℝ)) -
          6 * (2171139549275033092439 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3699107142389 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3699107142389 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3699107142389 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_176 :
    ((4400706843271805573 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10521836246531778932779 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((852561568430141 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1643283369413787703769 / 5000000000000000000000 : ℝ)) -
              6 * (135299506569951335849 / 625000000000000000000 : ℝ)))) ≤
      Vfield (465191185897 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (465191185897 / 4000000000000 : ℝ)) =
      Real.log (4465191185897 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((465191185897 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (487691185897 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4400706843271805573 / 40000000000000000000 : ℝ) ≤
      Real.log (4465191185897 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (487691185897 / 4000000000000 : ℝ) ≤
      (-(10521836246531778932779 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (487691185897 / 4000000000000 : ℝ) = (487691185897 / 250000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (487691185897 / 250000000000 : ℝ) ≤
            (3341107359468221067221 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (852561568430141 / 2500000000000000 : ℝ) ≤ Real.sqrt (465191185897 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (465191185897 / 4000000000000 : ℝ) ≤ (3410246273720567 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (465191185897 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau238 :
    Real.arctan (3410246273720567 / 10000000000000000 : ℝ) ≤
      (1643283369413787703769 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1643283369413787703769 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3410246273720567 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3410246273720567 : ℝ) =
              (3410246273720567 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau238)
  have hz1 :
    (10000000000000000 / 3410246273720567 : ℝ) ≤
      1 / Real.sqrt (465191185897 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3410246273720567 : ℝ) =
          1 / (3410246273720567 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 852561568430141 : ℝ) ≤
      (135299506569951335849 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (465191185897 / 4000000000000 : ℝ) ≤
      (187500000000000 / 852561568430141 : ℝ) := by
    rw [show
        (187500000000000 / 852561568430141 : ℝ) =
          (3 / 40) / (852561568430141 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1643283369413787703769 / 5000000000000000000000 : ℝ)) -
        6 * (135299506569951335849 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (465191185897 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (465191185897 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((852561568430141 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1643283369413787703769 / 5000000000000000000000 : ℝ)) -
          6 * (135299506569951335849 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (465191185897 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (465191185897 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (465191185897 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_177 :
    ((1106451725023094177469 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10493183176854784838949 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3420504272016681 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3295753160068787053413 / 10000000000000000000000 : ℝ)) -
              6 * (431700003932662026033 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (3743951831963 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3743951831963 / 32000000000000 : ℝ)) =
      Real.log (35743951831963 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3743951831963 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3923951831963 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1106451725023094177469 / 10000000000000000000000 : ℝ) ≤
      Real.log (35743951831963 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3923951831963 / 32000000000000 : ℝ) ≤
      (-(10493183176854784838949 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3923951831963 / 32000000000000 : ℝ) = (3923951831963 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3923951831963 / 2000000000000 : ℝ) ≤
            (3369760429145215161051 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3420504272016681 / 10000000000000000 : ℝ) ≤ Real.sqrt (3743951831963 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3743951831963 / 32000000000000 : ℝ) ≤ (855126068004171 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3743951831963 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau239 :
    Real.arctan (855126068004171 / 2500000000000000 : ℝ) ≤
      (3295753160068787053413 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3295753160068787053413 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 855126068004171 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 855126068004171 : ℝ) =
              (855126068004171 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau239)
  have hz1 :
    (2500000000000000 / 855126068004171 : ℝ) ≤
      1 / Real.sqrt (3743951831963 / 32000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 855126068004171 : ℝ) = 1 / (855126068004171 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1140168090672227 : ℝ) ≤
      (431700003932662026033 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3743951831963 / 32000000000000 : ℝ) ≤
      (250000000000000 / 1140168090672227 : ℝ) := by
    rw [show
        (250000000000000 / 1140168090672227 : ℝ) =
          (3 / 40) / (3420504272016681 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3295753160068787053413 / 10000000000000000000000 : ℝ)) -
        6 * (431700003932662026033 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3743951831963 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3743951831963 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3420504272016681 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3295753160068787053413 / 10000000000000000000000 : ℝ)) -
          6 * (431700003932662026033 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (3743951831963 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3743951831963 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3743951831963 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_178 :
    ((222544560823413658539 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2092938674339300144207 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((686146319740731 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (66098127401491722431 / 200000000000000000000 : ℝ)) -
              6 * (1076131246361408251279 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (15065496707 / 128000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (15065496707 / 128000000000 : ℝ)) =
      Real.log (143065496707 / 128000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((15065496707 / 128000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (15785496707 / 128000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (222544560823413658539 / 2000000000000000000000 : ℝ) ≤
      Real.log (143065496707 / 128000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (15785496707 / 128000000000 : ℝ) ≤
      (-(2092938674339300144207 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (15785496707 / 128000000000 : ℝ) = (15785496707 / 8000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15785496707 / 8000000000 : ℝ) ≤
            (679650046860699855793 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (686146319740731 / 2000000000000000 : ℝ) ≤ Real.sqrt (15065496707 / 128000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (15065496707 / 128000000000 : ℝ) ≤ (1715365799351829 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (15065496707 / 128000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau240 :
    Real.arctan (1715365799351829 / 5000000000000000 : ℝ) ≤
      (66098127401491722431 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (66098127401491722431 / 200000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1715365799351829 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1715365799351829 : ℝ) =
              (1715365799351829 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau240)
  have hz1 :
    (5000000000000000 / 1715365799351829 : ℝ) ≤ 1 / Real.sqrt (15065496707 / 128000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1715365799351829 : ℝ) = 1 / (1715365799351829 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 228715439913577 : ℝ) ≤
      (1076131246361408251279 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (15065496707 / 128000000000 : ℝ) ≤
      (50000000000000 / 228715439913577 : ℝ) := by
    rw [show
        (50000000000000 / 228715439913577 : ℝ) =
          (3 / 40) / (686146319740731 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (66098127401491722431 / 200000000000000000000 : ℝ)) -
        6 * (1076131246361408251279 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (15065496707 / 128000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (15065496707 / 128000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((686146319740731 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (66098127401491722431 / 200000000000000000000 : ℝ)) -
          6 * (1076131246361408251279 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (15065496707 / 128000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (15065496707 / 128000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (15065496707 / 128000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_179 :
    ((1118989953032259600469 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20872729962077034974551 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3440928527273287 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3314026655088241252493 / 10000000000000000000000 : ℝ)) -
              6 * (429215748043235457857 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (3788796521537 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3788796521537 / 32000000000000 : ℝ)) =
      Real.log (35788796521537 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3788796521537 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3968796521537 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1118989953032259600469 / 10000000000000000000000 : ℝ) ≤
      Real.log (35788796521537 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3968796521537 / 32000000000000 : ℝ) ≤
      (-(20872729962077034974551 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3968796521537 / 32000000000000 : ℝ) = (3968796521537 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3968796521537 / 2000000000000 : ℝ) ≤
            (6853157249922965025449 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3440928527273287 / 10000000000000000 : ℝ) ≤ Real.sqrt (3788796521537 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3788796521537 / 32000000000000 : ℝ) ≤ (344092852727329 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3788796521537 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau241 :
    Real.arctan (344092852727329 / 1000000000000000 : ℝ) ≤
      (3314026655088241252493 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3314026655088241252493 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 344092852727329 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 344092852727329 : ℝ) =
              (344092852727329 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau241)
  have hz1 :
    (1000000000000000 / 344092852727329 : ℝ) ≤
      1 / Real.sqrt (3788796521537 / 32000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 344092852727329 : ℝ) = 1 / (344092852727329 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3440928527273287 : ℝ) ≤
      (429215748043235457857 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3788796521537 / 32000000000000 : ℝ) ≤
      (750000000000000 / 3440928527273287 : ℝ) := by
    rw [show
        (750000000000000 / 3440928527273287 : ℝ) =
          (3 / 40) / (3440928527273287 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3314026655088241252493 / 10000000000000000000000 : ℝ)) -
        6 * (429215748043235457857 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3788796521537 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3788796521537 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3440928527273287 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3314026655088241252493 / 10000000000000000000000 : ℝ)) -
          6 * (429215748043235457857 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (3788796521537 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3788796521537 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3788796521537 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_180 :
    ((45010127067671446827 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20816392372260701008297 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3451095327176937 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (332311429720360928943 / 1000000000000000000000 : ℝ)) -
              6 * (2139947993750407451587 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (952804716581 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (952804716581 / 8000000000000 : ℝ)) =
      Real.log (8952804716581 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((952804716581 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (997804716581 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (45010127067671446827 / 400000000000000000000 : ℝ) ≤
      Real.log (8952804716581 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (997804716581 / 8000000000000 : ℝ) ≤
      (-(20816392372260701008297 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (997804716581 / 8000000000000 : ℝ) = (997804716581 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (997804716581 / 500000000000 : ℝ) ≤
            (6909494839739298991703 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3451095327176937 / 10000000000000000 : ℝ) ≤ Real.sqrt (952804716581 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (952804716581 / 8000000000000 : ℝ) ≤ (172554766358847 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (952804716581 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau242 :
    Real.arctan (172554766358847 / 500000000000000 : ℝ) ≤
      (332311429720360928943 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (332311429720360928943 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 172554766358847 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 172554766358847 : ℝ) =
              (172554766358847 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau242)
  have hz1 :
    (500000000000000 / 172554766358847 : ℝ) ≤ 1 / Real.sqrt (952804716581 / 8000000000000 : ℝ) := by
    rw [show (500000000000000 / 172554766358847 : ℝ) = 1 / (172554766358847 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1150365109058979 : ℝ) ≤
      (2139947993750407451587 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (952804716581 / 8000000000000 : ℝ) ≤
      (250000000000000 / 1150365109058979 : ℝ) := by
    rw [show
        (250000000000000 / 1150365109058979 : ℝ) =
          (3 / 40) / (3451095327176937 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (332311429720360928943 / 1000000000000000000000 : ℝ)) -
        6 * (2139947993750407451587 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (952804716581 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (952804716581 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3451095327176937 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (332311429720360928943 / 1000000000000000000000 : ℝ)) -
          6 * (2139947993750407451587 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (952804716581 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (952804716581 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (952804716581 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
