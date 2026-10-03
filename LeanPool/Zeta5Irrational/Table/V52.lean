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

/-! # V52: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_625 :
    ((2730877782592370590811 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3116169747917816613287 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1704860051870497 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ))) -
              6 * (877577784756869561493 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23252382371711 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23252382371711 / 32000000000000 : ℝ)) =
      Real.log (55252382371711 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23252382371711 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23432382371711 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2730877782592370590811 / 5000000000000000000000 : ℝ) ≤
      Real.log (55252382371711 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23432382371711 / 32000000000000 : ℝ) ≤
      (-(3116169747917816613287 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23432382371711 / 32000000000000 : ℝ) = (23432382371711 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23432382371711 / 16000000000000 : ℝ) ≤
            (3815302055082183386713 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1704860051870497 / 2000000000000000 : ℝ) ≤ Real.sqrt (23252382371711 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23252382371711 / 32000000000000 : ℝ) ≤ (1065537532419061 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23252382371711 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1022 :
    Real.arctan (4262150129676244 / 11570077908815025 : ℝ) ≤
      (3529515644499602674989 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1021 :
    Real.arctan (1065537532419061 / 1250000000000000 : ℝ) ≤
      (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (262803116352601 / 200000000000000 : ℝ) ≤
          Real.sqrt (1 + (1065537532419061 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1065537532419061 / 1250000000000000 : ℝ) /
                (1 + (262803116352601 / 200000000000000 : ℝ)) =
              (4262150129676244 / 11570077908815025 : ℝ)
            by
        norm_num];
        exact hau1022)
  have hat1 :
    (Real.pi / 2 - (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 1065537532419061 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 1065537532419061 : ℝ) =
              (1065537532419061 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau1021)
  have hz1 :
    (1250000000000000 / 1065537532419061 : ℝ) ≤
      1 / Real.sqrt (23252382371711 / 32000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 1065537532419061 : ℝ) = 1 / (1065537532419061 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1704860051870497 : ℝ) ≤
      (877577784756869561493 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23252382371711 / 32000000000000 : ℝ) ≤
      (150000000000000 / 1704860051870497 : ℝ) := by
    rw [show
        (150000000000000 / 1704860051870497 : ℝ) =
          (3 / 40) / (1704860051870497 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ))) -
        6 * (877577784756869561493 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23252382371711 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23252382371711 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1704860051870497 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ))) -
          6 * (877577784756869561493 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (23252382371711 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23252382371711 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23252382371711 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_626 :
    ((546726995479048066533 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(77579298971171939033 / 250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8529884797410073 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ))) -
              6 * (219251543692524048579 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (5820714772567 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5820714772567 / 8000000000000 : ℝ)) =
      Real.log (13820714772567 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5820714772567 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5865714772567 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (546726995479048066533 / 1000000000000000000000 : ℝ) ≤
      Real.log (13820714772567 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5865714772567 / 8000000000000 : ℝ) ≤
      (-(77579298971171939033 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5865714772567 / 8000000000000 : ℝ) = (5865714772567 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5865714772567 / 4000000000000 : ℝ) ≤
            (95707496103828060967 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8529884797410073 / 10000000000000000 : ℝ) ≤ Real.sqrt (5820714772567 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5820714772567 / 8000000000000 : ℝ) ≤ (2132471199352519 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5820714772567 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1024 :
    Real.arctan (8529884797410076 / 23143779314074301 : ℝ) ≤
      (1765566185380807726961 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1023 :
    Real.arctan (2132471199352519 / 2500000000000000 : ℝ) ≤
      (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13143779314074301 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2132471199352519 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2132471199352519 / 2500000000000000 : ℝ) /
                (1 + (13143779314074301 / 10000000000000000 : ℝ)) =
              (8529884797410076 / 23143779314074301 : ℝ)
            by
        norm_num];
        exact hau1024)
  have hat1 :
    (Real.pi / 2 - (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2132471199352519 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2132471199352519 : ℝ) =
              (2132471199352519 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1023)
  have hz1 :
    (2500000000000000 / 2132471199352519 : ℝ) ≤
      1 / Real.sqrt (5820714772567 / 8000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2132471199352519 : ℝ) = 1 / (2132471199352519 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8529884797410073 : ℝ) ≤
      (219251543692524048579 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5820714772567 / 8000000000000 : ℝ) ≤
      (750000000000000 / 8529884797410073 : ℝ) := by
    rw [show
        (750000000000000 / 8529884797410073 : ℝ) =
          (3 / 40) / (8529884797410073 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ))) -
        6 * (219251543692524048579 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5820714772567 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5820714772567 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8529884797410073 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ))) -
          6 * (219251543692524048579 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (5820714772567 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5820714772567 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5820714772567 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_627 :
    ((5472781305222789424267 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3090191042100093015749 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8535465681647259 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ))) -
              6 * (175287136058003471421 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (932533432353 / 1280000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (932533432353 / 1280000000000 : ℝ)) =
      Real.log (2212533432353 / 1280000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((932533432353 / 1280000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (939733432353 / 1280000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5472781305222789424267 / 10000000000000000000000 : ℝ) ≤
      Real.log (2212533432353 / 1280000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (939733432353 / 1280000000000 : ℝ) ≤
      (-(3090191042100093015749 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (939733432353 / 1280000000000 : ℝ) = (939733432353 / 640000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (939733432353 / 640000000000 : ℝ) ≤
            (3841280760899906984251 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8535465681647259 / 10000000000000000 : ℝ) ≤ Real.sqrt (932533432353 / 1280000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (932533432353 / 1280000000000 : ℝ) ≤ (4267732840823631 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (932533432353 / 1280000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau1026 :
    Real.arctan (251043108283743 / 680805935643029 : ℝ) ≤
      (3532747148789359859367 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1025 :
    Real.arctan (4267732840823631 / 5000000000000000 : ℝ) ≤
      (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6573700905931493 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4267732840823631 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4267732840823631 / 5000000000000000 : ℝ) /
                (1 + (6573700905931493 / 5000000000000000 : ℝ)) =
              (251043108283743 / 680805935643029 : ℝ)
            by
        norm_num];
        exact hau1026)
  have hat1 :
    (Real.pi / 2 - (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4267732840823631 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4267732840823631 : ℝ) =
              (4267732840823631 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1025)
  have hz1 :
    (5000000000000000 / 4267732840823631 : ℝ) ≤
      1 / Real.sqrt (932533432353 / 1280000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4267732840823631 : ℝ) = 1 / (4267732840823631 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2845155227215753 : ℝ) ≤
      (175287136058003471421 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (932533432353 / 1280000000000 : ℝ) ≤
      (250000000000000 / 2845155227215753 : ℝ) := by
    rw [show
        (250000000000000 / 2845155227215753 : ℝ) =
          (3 / 40) / (8535465681647259 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ))) -
        6 * (175287136058003471421 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (932533432353 / 1280000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (932533432353 / 1280000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8535465681647259 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ))) -
          6 * (175287136058003471421 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (932533432353 / 1280000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (932533432353 / 1280000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (932533432353 / 1280000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_628 :
    ((5478289619829812308189 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(769306738482647776489 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2135260729806619 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (441794997850047114757 / 1250000000000000000000 : ℝ))) -
              6 * (218966574423277628579 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (11671906263691 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11671906263691 / 16000000000000 : ℝ)) =
      Real.log (27671906263691 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11671906263691 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11761906263691 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5478289619829812308189 / 10000000000000000000000 : ℝ) ≤
      Real.log (27671906263691 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11761906263691 / 16000000000000 : ℝ) ≤
      (-(769306738482647776489 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11761906263691 / 16000000000000 : ℝ) = (11761906263691 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11761906263691 / 8000000000000 : ℝ) ≤
            (963561212267352223511 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2135260729806619 / 2500000000000000 : ℝ) ≤ Real.sqrt (11671906263691 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11671906263691 / 16000000000000 : ℝ) ≤
      (8541042919226479 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11671906263691 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1028 :
    Real.arctan (8541042919226479 / 23151023311821356 : ℝ) ≤
      (441794997850047114757 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1027 :
    Real.arctan (8541042919226479 / 10000000000000000 : ℝ) ≤
      (2 * (441794997850047114757 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3287755827955339 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8541042919226479 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8541042919226479 / 10000000000000000 : ℝ) /
                (1 + (3287755827955339 / 2500000000000000 : ℝ)) =
              (8541042919226479 / 23151023311821356 : ℝ)
            by
        norm_num];
        exact hau1028)
  have hat1 :
    (Real.pi / 2 - (2 * (441794997850047114757 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8541042919226479 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8541042919226479 : ℝ) =
              (8541042919226479 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1027)
  have hz1 :
    (10000000000000000 / 8541042919226479 : ℝ) ≤
      1 / Real.sqrt (11671906263691 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8541042919226479 : ℝ) =
          1 / (8541042919226479 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2135260729806619 : ℝ) ≤
      (218966574423277628579 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11671906263691 / 16000000000000 : ℝ) ≤
      (187500000000000 / 2135260729806619 : ℝ) := by
    rw [show
        (187500000000000 / 2135260729806619 : ℝ) =
          (3 / 40) / (2135260729806619 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (441794997850047114757 / 1250000000000000000000 : ℝ))) -
        6 * (218966574423277628579 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11671906263691 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11671906263691 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2135260729806619 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (441794997850047114757 / 1250000000000000000000 : ℝ))) -
          6 * (218966574423277628579 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (11671906263691 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11671906263691 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11671906263691 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_629 :
    ((5483794901954164421831 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(38303495634517765457 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2136654129321697 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ))) -
              6 * (875298023372310254261 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23374289245939 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23374289245939 / 32000000000000 : ℝ)) =
      Real.log (55374289245939 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23374289245939 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23554289245939 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5483794901954164421831 / 10000000000000000000000 : ℝ) ≤
      Real.log (55374289245939 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23554289245939 / 32000000000000 : ℝ) ≤
      (-(38303495634517765457 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23554289245939 / 32000000000000 : ℝ) = (23554289245939 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23554289245939 / 16000000000000 : ℝ) ≤
            (48339901902982234543 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2136654129321697 / 2500000000000000 : ℝ) ≤ Real.sqrt (23374289245939 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23374289245939 / 32000000000000 : ℝ) ≤
      (8546616517286791 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23374289245939 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1030 :
    Real.arctan (8546616517286791 / 23154643814773525 : ℝ) ≤
      (3535970876998488086731 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1029 :
    Real.arctan (8546616517286791 / 10000000000000000 : ℝ) ≤
      (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (526185752590941 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (8546616517286791 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8546616517286791 / 10000000000000000 : ℝ) /
                (1 + (526185752590941 / 400000000000000 : ℝ)) =
              (8546616517286791 / 23154643814773525 : ℝ)
            by
        norm_num];
        exact hau1030)
  have hat1 :
    (Real.pi / 2 - (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8546616517286791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8546616517286791 : ℝ) =
              (8546616517286791 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1029)
  have hz1 :
    (10000000000000000 / 8546616517286791 : ℝ) ≤
      1 / Real.sqrt (23374289245939 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8546616517286791 : ℝ) =
          1 / (8546616517286791 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2136654129321697 : ℝ) ≤
      (875298023372310254261 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23374289245939 / 32000000000000 : ℝ) ≤
      (187500000000000 / 2136654129321697 : ℝ) := by
    rw [show
        (187500000000000 / 2136654129321697 : ℝ) =
          (3 / 40) / (2136654129321697 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ))) -
        6 * (875298023372310254261 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23374289245939 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23374289245939 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2136654129321697 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ))) -
          6 * (875298023372310254261 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (23374289245939 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23374289245939 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23374289245939 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_630 :
    ((5489297154932943295337 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(122053963567387008637 / 400000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1710437296588799 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (884394958893463844413 / 2500000000000000000000 : ℝ))) -
              6 * (174946170747382495469 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (1462797872781 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1462797872781 / 2000000000000 : ℝ)) =
      Real.log (3462797872781 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1462797872781 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1474047872781 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5489297154932943295337 / 10000000000000000000000 : ℝ) ≤
      Real.log (3462797872781 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1474047872781 / 2000000000000 : ℝ) ≤
      (-(122053963567387008637 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (1474047872781 / 2000000000000 : ℝ) = (1474047872781 / 1000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1474047872781 / 1000000000000 : ℝ) ≤
            (155204908552612991363 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1710437296588799 / 2000000000000000 : ℝ) ≤ Real.sqrt (1462797872781 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1462797872781 / 2000000000000 : ℝ) ≤ (4276093241471999 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1462797872781 / 2000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1032 :
    Real.arctan (4276093241471999 / 11579131660771237 : ℝ) ≤
      (884394958893463844413 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1031 :
    Real.arctan (4276093241471999 / 5000000000000000 : ℝ) ≤
      (2 * (884394958893463844413 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6579131660771237 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4276093241471999 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4276093241471999 / 5000000000000000 : ℝ) /
                (1 + (6579131660771237 / 5000000000000000 : ℝ)) =
              (4276093241471999 / 11579131660771237 : ℝ)
            by
        norm_num];
        exact hau1032)
  have hat1 :
    (Real.pi / 2 - (2 * (884394958893463844413 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4276093241471999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4276093241471999 : ℝ) =
              (4276093241471999 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1031)
  have hz1 :
    (5000000000000000 / 4276093241471999 : ℝ) ≤
      1 / Real.sqrt (1462797872781 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4276093241471999 : ℝ) = 1 / (4276093241471999 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1710437296588799 : ℝ) ≤
      (174946170747382495469 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1462797872781 / 2000000000000 : ℝ) ≤
      (150000000000000 / 1710437296588799 : ℝ) := by
    rw [show
        (150000000000000 / 1710437296588799 : ℝ) =
          (3 / 40) / (1710437296588799 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (884394958893463844413 / 2500000000000000000000 : ℝ))) -
        6 * (174946170747382495469 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1462797872781 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1462797872781 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1710437296588799 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (884394958893463844413 / 2500000000000000000000 : ℝ))) -
          6 * (174946170747382495469 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (1462797872781 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1462797872781 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1462797872781 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_631 :
    ((1098959276419548204243 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3038435225960614059479 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4278876411645369 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (884796715675760448579 / 2500000000000000000000 : ℝ))) -
              6 * (437082392606239601383 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (23435242683053 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23435242683053 / 32000000000000 : ℝ)) =
      Real.log (55435242683053 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23435242683053 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23615242683053 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1098959276419548204243 / 2000000000000000000000 : ℝ) ≤
      Real.log (55435242683053 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23615242683053 / 32000000000000 : ℝ) ≤
      (-(3038435225960614059479 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23615242683053 / 32000000000000 : ℝ) = (23615242683053 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23615242683053 / 16000000000000 : ℝ) ≤
            (3893036577039385940521 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4278876411645369 / 5000000000000000 : ℝ) ≤ Real.sqrt (23435242683053 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23435242683053 / 32000000000000 : ℝ) ≤
      (8557752823290741 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23435242683053 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1034 :
    Real.arctan (8557752823290741 / 23161881832950052 : ℝ) ≤
      (884796715675760448579 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1033 :
    Real.arctan (8557752823290741 / 10000000000000000 : ℝ) ≤
      (2 * (884796715675760448579 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3290470458237513 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8557752823290741 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8557752823290741 / 10000000000000000 : ℝ) /
                (1 + (3290470458237513 / 2500000000000000 : ℝ)) =
              (8557752823290741 / 23161881832950052 : ℝ)
            by
        norm_num];
        exact hau1034)
  have hat1 :
    (Real.pi / 2 - (2 * (884796715675760448579 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8557752823290741 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8557752823290741 : ℝ) =
              (8557752823290741 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1033)
  have hz1 :
    (10000000000000000 / 8557752823290741 : ℝ) ≤
      1 / Real.sqrt (23435242683053 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8557752823290741 : ℝ) =
          1 / (8557752823290741 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1426292137215123 : ℝ) ≤
      (437082392606239601383 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23435242683053 / 32000000000000 : ℝ) ≤
      (125000000000000 / 1426292137215123 : ℝ) := by
    rw [show
        (125000000000000 / 1426292137215123 : ℝ) =
          (3 / 40) / (4278876411645369 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (884796715675760448579 / 2500000000000000000000 : ℝ))) -
        6 * (437082392606239601383 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23435242683053 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23435242683053 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4278876411645369 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (884796715675760448579 / 2500000000000000000000 : ℝ))) -
          6 * (437082392606239601383 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (23435242683053 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23435242683053 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23435242683053 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_632 :
    ((5500292586774656357943 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(184664185669970729 / 610351562500000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8563315545396609 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (708158392509814711217 / 2000000000000000000000 : ℝ))) -
              6 * (436799907120371740757 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2346571940161 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2346571940161 / 3200000000000 : ℝ)) =
      Real.log (5546571940161 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2346571940161 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2364571940161 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5500292586774656357943 / 10000000000000000000000 : ℝ) ≤
      Real.log (5546571940161 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2364571940161 / 3200000000000 : ℝ) ≤
      (-(184664185669970729 / 610351562500000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2364571940161 / 3200000000000 : ℝ) = (2364571940161 / 1600000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2364571940161 / 1600000000000 : ℝ) ≤
            (953597115474413959 / 2441406250000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8563315545396609 / 10000000000000000 : ℝ) ≤ Real.sqrt (2346571940161 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2346571940161 / 3200000000000 : ℝ) ≤ (2140828886349153 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2346571940161 / 3200000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1036 :
    Real.arctan (2854438515132204 / 7721833116605659 : ℝ) ≤
      (708158392509814711217 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1035 :
    Real.arctan (2140828886349153 / 2500000000000000 : ℝ) ≤
      (2 * (708158392509814711217 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13165499349816977 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2140828886349153 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2140828886349153 / 2500000000000000 : ℝ) /
                (1 + (13165499349816977 / 10000000000000000 : ℝ)) =
              (2854438515132204 / 7721833116605659 : ℝ)
            by
        norm_num];
        exact hau1036)
  have hat1 :
    (Real.pi / 2 - (2 * (708158392509814711217 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2140828886349153 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2140828886349153 : ℝ) =
              (2140828886349153 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1035)
  have hz1 :
    (2500000000000000 / 2140828886349153 : ℝ) ≤
      1 / Real.sqrt (2346571940161 / 3200000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2140828886349153 : ℝ) = 1 / (2140828886349153 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2854438515132203 : ℝ) ≤
      (436799907120371740757 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2346571940161 / 3200000000000 : ℝ) ≤
      (250000000000000 / 2854438515132203 : ℝ) := by
    rw [show
        (250000000000000 / 2854438515132203 : ℝ) =
          (3 / 40) / (8563315545396609 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (708158392509814711217 / 2000000000000000000000 : ℝ))) -
        6 * (436799907120371740757 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2346571940161 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2346571940161 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8563315545396609 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (708158392509814711217 / 2000000000000000000000 : ℝ))) -
          6 * (436799907120371740757 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (2346571940161 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2346571940161 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2346571940161 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_633 :
    ((5505785772284306800337 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3012657422447236628907 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8568874656308251 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ))) -
              6 * (109129492159939492009 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (23496196120167 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23496196120167 / 32000000000000 : ℝ)) =
      Real.log (55496196120167 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23496196120167 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23676196120167 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5505785772284306800337 / 10000000000000000000000 : ℝ) ≤
      Real.log (55496196120167 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23676196120167 / 32000000000000 : ℝ) ≤
      (-(3012657422447236628907 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23676196120167 / 32000000000000 : ℝ) = (23676196120167 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23676196120167 / 16000000000000 : ℝ) ≤
            (3918814380552763371093 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8568874656308251 / 10000000000000000 : ℝ) ≤
      Real.sqrt (23496196120167 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23496196120167 / 32000000000000 : ℝ) ≤ (4284437328154127 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23496196120167 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1038 :
    Real.arctan (8568874656308254 / 23169115872962841 : ℝ) ≤
      (3542395139261497851501 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1037 :
    Real.arctan (4284437328154127 / 5000000000000000 : ℝ) ≤
      (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13169115872962841 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4284437328154127 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4284437328154127 / 5000000000000000 : ℝ) /
                (1 + (13169115872962841 / 10000000000000000 : ℝ)) =
              (8568874656308254 / 23169115872962841 : ℝ)
            by
        norm_num];
        exact hau1038)
  have hat1 :
    (Real.pi / 2 - (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4284437328154127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4284437328154127 : ℝ) =
              (4284437328154127 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1037)
  have hz1 :
    (5000000000000000 / 4284437328154127 : ℝ) ≤
      1 / Real.sqrt (23496196120167 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4284437328154127 : ℝ) = 1 / (4284437328154127 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8568874656308251 : ℝ) ≤
      (109129492159939492009 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23496196120167 / 32000000000000 : ℝ) ≤
      (750000000000000 / 8568874656308251 : ℝ) := by
    rw [show
        (750000000000000 / 8568874656308251 : ℝ) =
          (3 / 40) / (8568874656308251 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ))) -
        6 * (109129492159939492009 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23496196120167 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23496196120167 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8568874656308251 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ))) -
          6 * (109129492159939492009 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (23496196120167 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23496196120167 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23496196120167 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_634 :
    ((5511275941941840616771 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2999793396511508222773 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1714886032609893 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (885999099244110855617 / 2500000000000000000000 : ℝ))) -
              6 * (872473150802591192013 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5881668209681 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5881668209681 / 8000000000000 : ℝ)) =
      Real.log (13881668209681 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5881668209681 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5926668209681 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5511275941941840616771 / 10000000000000000000000 : ℝ) ≤
      Real.log (13881668209681 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5926668209681 / 8000000000000 : ℝ) ≤
      (-(2999793396511508222773 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5926668209681 / 8000000000000 : ℝ) = (5926668209681 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5926668209681 / 4000000000000 : ℝ) ≤
            (3931678406488491777227 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1714886032609893 / 2000000000000000 : ℝ) ≤ Real.sqrt (5881668209681 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5881668209681 / 8000000000000 : ℝ) ≤ (2143607540762367 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5881668209681 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1040 :
    Real.arctan (8574430163049468 / 23172731403206113 : ℝ) ≤
      (885999099244110855617 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1039 :
    Real.arctan (2143607540762367 / 2500000000000000 : ℝ) ≤
      (2 * (885999099244110855617 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13172731403206113 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2143607540762367 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2143607540762367 / 2500000000000000 : ℝ) /
                (1 + (13172731403206113 / 10000000000000000 : ℝ)) =
              (8574430163049468 / 23172731403206113 : ℝ)
            by
        norm_num];
        exact hau1040)
  have hat1 :
    (Real.pi / 2 - (2 * (885999099244110855617 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2143607540762367 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2143607540762367 : ℝ) =
              (2143607540762367 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1039)
  have hz1 :
    (2500000000000000 / 2143607540762367 : ℝ) ≤
      1 / Real.sqrt (5881668209681 / 8000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2143607540762367 : ℝ) = 1 / (2143607540762367 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 571628677536631 : ℝ) ≤
      (872473150802591192013 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5881668209681 / 8000000000000 : ℝ) ≤
      (50000000000000 / 571628677536631 : ℝ) := by
    rw [show
        (50000000000000 / 571628677536631 : ℝ) =
          (3 / 40) / (1714886032609893 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (885999099244110855617 / 2500000000000000000000 : ℝ))) -
        6 * (872473150802591192013 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5881668209681 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5881668209681 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1714886032609893 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (885999099244110855617 / 2500000000000000000000 : ℝ))) -
          6 * (872473150802591192013 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5881668209681 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5881668209681 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5881668209681 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_635 :
    ((1379190774764237213347 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2986945897633933050071 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((33515554971177 / 39062500000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ))) -
              6 * (174382290259931083323 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (23557149557281 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23557149557281 / 32000000000000 : ℝ)) =
      Real.log (55557149557281 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23557149557281 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23737149557281 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1379190774764237213347 / 2500000000000000000000 : ℝ) ≤
      Real.log (55557149557281 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23737149557281 / 32000000000000 : ℝ) ≤
      (-(2986945897633933050071 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23737149557281 / 32000000000000 : ℝ) = (23737149557281 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23737149557281 / 16000000000000 : ℝ) ≤
            (3944525905366066949929 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (33515554971177 / 39062500000000 : ℝ) ≤ Real.sqrt (23557149557281 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23557149557281 / 32000000000000 : ℝ) ≤ (1715996414524263 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23557149557281 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1042 :
    Real.arctan (1715996414524263 / 4635269188272827 : ℝ) ≤
      (1772797869908340061831 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1041 :
    Real.arctan (1715996414524263 / 2000000000000000 : ℝ) ≤
      (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2635269188272827 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1715996414524263 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1715996414524263 / 2000000000000000 : ℝ) /
                (1 + (2635269188272827 / 2000000000000000 : ℝ)) =
              (1715996414524263 / 4635269188272827 : ℝ)
            by
        norm_num];
        exact hau1042)
  have hat1 :
    (Real.pi / 2 - (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1715996414524263 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1715996414524263 : ℝ) =
              (1715996414524263 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1041)
  have hz1 :
    (2000000000000000 / 1715996414524263 : ℝ) ≤
      1 / Real.sqrt (23557149557281 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1715996414524263 : ℝ) = 1 / (1715996414524263 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (976562500000 / 11171851657059 : ℝ) ≤
      (174382290259931083323 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23557149557281 / 32000000000000 : ℝ) ≤
      (976562500000 / 11171851657059 : ℝ) := by
    rw [show
        (976562500000 / 11171851657059 : ℝ) = (3 / 40) / (33515554971177 / 39062500000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ))) -
        6 * (174382290259931083323 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23557149557281 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23557149557281 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((33515554971177 / 39062500000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ))) -
          6 * (174382290259931083323 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (23557149557281 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23557149557281 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23557149557281 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_636 :
    ((5522247246933877305379 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2974114883402715778061 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1073191299000277 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ))) -
              6 * (435675417638097174757 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (11793813137919 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11793813137919 / 16000000000000 : ℝ)) =
      Real.log (27793813137919 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11793813137919 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11883813137919 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5522247246933877305379 / 10000000000000000000000 : ℝ) ≤
      Real.log (27793813137919 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11883813137919 / 16000000000000 : ℝ) ≤
      (-(2974114883402715778061 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11883813137919 / 16000000000000 : ℝ) = (11883813137919 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11883813137919 / 8000000000000 : ℝ) ≤
            (3957356919597284221939 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1073191299000277 / 1250000000000000 : ℝ) ≤ Real.sqrt (11793813137919 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11793813137919 / 16000000000000 : ℝ) ≤
      (8585530392002219 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11793813137919 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1044 :
    Real.arctan (8585530392002219 / 23179959488253131 : ℝ) ≤
      (3547193171891676928569 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1043 :
    Real.arctan (8585530392002219 / 10000000000000000 : ℝ) ≤
      (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13179959488253131 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8585530392002219 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8585530392002219 / 10000000000000000 : ℝ) /
                (1 + (13179959488253131 / 10000000000000000 : ℝ)) =
              (8585530392002219 / 23179959488253131 : ℝ)
            by
        norm_num];
        exact hau1044)
  have hat1 :
    (Real.pi / 2 - (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8585530392002219 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8585530392002219 : ℝ) =
              (8585530392002219 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1043)
  have hz1 :
    (10000000000000000 / 8585530392002219 : ℝ) ≤
      1 / Real.sqrt (11793813137919 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8585530392002219 : ℝ) =
          1 / (8585530392002219 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 1073191299000277 : ℝ) ≤
      (435675417638097174757 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11793813137919 / 16000000000000 : ℝ) ≤
      (93750000000000 / 1073191299000277 : ℝ) := by
    rw [show
        (93750000000000 / 1073191299000277 : ℝ) =
          (3 / 40) / (1073191299000277 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ))) -
        6 * (435675417638097174757 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11793813137919 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11793813137919 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1073191299000277 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ))) -
          6 * (435675417638097174757 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (11793813137919 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11793813137919 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11793813137919 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
