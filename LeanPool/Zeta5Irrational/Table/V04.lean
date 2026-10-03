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

/-! # V04: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_49 :
    ((9367832807386358049 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(37075617054825365057033 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1375219235839097 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (683323396048354980263 / 5000000000000000000000 : ℝ)) -
              6 * (2 * (62409962799765955357 / 250000000000000000000 : ℝ))))) ≤
      Vfield (605192942919 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (605192942919 / 32000000000000 : ℝ)) =
      Real.log (32605192942919 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((605192942919 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (785192942919 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (9367832807386358049 / 500000000000000000000 : ℝ) ≤
      Real.log (32605192942919 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (785192942919 / 32000000000000 : ℝ) ≤
      (-(37075617054825365057033 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (785192942919 / 32000000000000 : ℝ) = (785192942919 / 500000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (785192942919 / 500000000000 : ℝ) ≤
            (4513213763174634942967 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1375219235839097 / 10000000000000000 : ℝ) ≤ Real.sqrt (605192942919 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (605192942919 / 32000000000000 : ℝ) ≤ (13752192358391 / 100000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (605192942919 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau106 :
    Real.arctan (13752192358391 / 100000000000000 : ℝ) ≤
      (683323396048354980263 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (683323396048354980263 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (100000000000000 / 13752192358391 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (100000000000000 / 13752192358391 : ℝ) =
              (13752192358391 / 100000000000000 : ℝ)
            by
        norm_num];
        exact hau106)
  have hz1 :
    (100000000000000 / 13752192358391 : ℝ) ≤ 1 / Real.sqrt (605192942919 / 32000000000000 : ℝ) := by
    rw [show (100000000000000 / 13752192358391 : ℝ) = 1 / (13752192358391 / 100000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau107 :
    Real.arctan (1500000000000000000000000000000 / 5883314432594533368393189293789 : ℝ) ≤
      (62409962799765955357 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1375219235839097 : ℝ) ≤
      (2 * (62409962799765955357 / 250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2278092015637637 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1375219235839097 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1375219235839097 : ℝ) /
                (1 + (2278092015637637 / 2000000000000000 : ℝ)) =
              (1500000000000000000000000000000 / 5883314432594533368393189293789 : ℝ)
            by
        norm_num];
        exact hau107)
  have hz2 :
    (3 / 40) / Real.sqrt (605192942919 / 32000000000000 : ℝ) ≤
      (750000000000000 / 1375219235839097 : ℝ) := by
    rw [show
        (750000000000000 / 1375219235839097 : ℝ) =
          (3 / 40) / (1375219235839097 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (683323396048354980263 / 5000000000000000000000 : ℝ)) -
        6 * (2 * (62409962799765955357 / 250000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (605192942919 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (605192942919 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1375219235839097 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (683323396048354980263 / 5000000000000000000000 : ℝ)) -
          6 * (2 * (62409962799765955357 / 250000000000000000000 : ℝ)))) ≤
      Real.sqrt (605192942919 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (605192942919 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (605192942919 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_50 :
    ((19054250695858538469 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7388834199649120704961 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((173371626818641 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1378180571218092944099 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (1239276500758368893079 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (153895531447 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (153895531447 / 8000000000000 : ℝ)) =
      Real.log (8153895531447 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((153895531447 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (198895531447 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (19054250695858538469 / 1000000000000000000000 : ℝ) ≤
      Real.log (8153895531447 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (198895531447 / 8000000000000 : ℝ) ≤
      (-(7388834199649120704961 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (198895531447 / 8000000000000 : ℝ) = (198895531447 / 125000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (198895531447 / 125000000000 : ℝ) ≤
            (928931963950879295039 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (173371626818641 / 1250000000000000 : ℝ) ≤ Real.sqrt (153895531447 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (153895531447 / 8000000000000 : ℝ) ≤ (1386973014549131 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (153895531447 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau108 :
    Real.arctan (1386973014549131 / 10000000000000000 : ℝ) ≤
      (1378180571218092944099 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1378180571218092944099 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1386973014549131 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1386973014549131 : ℝ) =
              (1386973014549131 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau108)
  have hz1 :
    (10000000000000000 / 1386973014549131 : ℝ) ≤
      1 / Real.sqrt (153895531447 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1386973014549131 : ℝ) =
          1 / (1386973014549131 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau109 :
    Real.arctan (312500000000000000000000000000 / 1234891668870499026098149566991 : ℝ) ≤
      (1239276500758368893079 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (93750000000000 / 173371626818641 : ℝ) ≤
      (2 * (1239276500758368893079 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11368404245793053 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (93750000000000 / 173371626818641 : ℝ) ^ 2))
      (by
        rw [show
            (93750000000000 / 173371626818641 : ℝ) /
                (1 + (11368404245793053 / 10000000000000000 : ℝ)) =
              (312500000000000000000000000000 / 1234891668870499026098149566991 : ℝ)
            by
        norm_num];
        exact hau109)
  have hz2 :
    (3 / 40) / Real.sqrt (153895531447 / 8000000000000 : ℝ) ≤
      (93750000000000 / 173371626818641 : ℝ) := by
    rw [show
        (93750000000000 / 173371626818641 : ℝ) =
          (3 / 40) / (173371626818641 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1378180571218092944099 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (1239276500758368893079 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (153895531447 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (153895531447 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((173371626818641 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1378180571218092944099 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (1239276500758368893079 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (153895531447 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (153895531447 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (153895531447 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_51 :
    ((19691116530249562487 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(36686351439827391625567 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1410186702539329 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (140094889551191353099 / 1000000000000000000000 : ℝ)) -
              6 * (2 * (1221993650998643614353 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (318180245763 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (318180245763 / 16000000000000 : ℝ)) =
      Real.log (16318180245763 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((318180245763 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (408180245763 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (19691116530249562487 / 1000000000000000000000 : ℝ) ≤
      Real.log (16318180245763 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (408180245763 / 16000000000000 : ℝ) ≤
      (-(36686351439827391625567 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (408180245763 / 16000000000000 : ℝ) = (408180245763 / 250000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (408180245763 / 250000000000 : ℝ) ≤
            (4902479378172608374433 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1410186702539329 / 10000000000000000 : ℝ) ≤ Real.sqrt (318180245763 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (318180245763 / 16000000000000 : ℝ) ≤ (352546675634833 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (318180245763 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau110 :
    Real.arctan (352546675634833 / 2500000000000000 : ℝ) ≤
      (140094889551191353099 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (140094889551191353099 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 352546675634833 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 352546675634833 : ℝ) =
              (352546675634833 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau110)
  have hz1 :
    (2500000000000000 / 352546675634833 : ℝ) ≤
      1 / Real.sqrt (318180245763 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 352546675634833 : ℝ) = 1 / (352546675634833 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau111 :
    Real.arctan (7500000000000000000000000000000 / 30074113379675286162750332138029 : ℝ) ≤
      (1221993650998643614353 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1410186702539329 : ℝ) ≤
      (2 * (1221993650998643614353 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11326334538200301 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1410186702539329 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1410186702539329 : ℝ) /
                (1 + (11326334538200301 / 10000000000000000 : ℝ)) =
              (7500000000000000000000000000000 / 30074113379675286162750332138029 : ℝ)
            by
        norm_num];
        exact hau111)
  have hz2 :
    (3 / 40) / Real.sqrt (318180245763 / 16000000000000 : ℝ) ≤
      (750000000000000 / 1410186702539329 : ℝ) := by
    rw [show
        (750000000000000 / 1410186702539329 : ℝ) =
          (3 / 40) / (1410186702539329 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (140094889551191353099 / 1000000000000000000000 : ℝ)) -
        6 * (2 * (1221993650998643614353 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (318180245763 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (318180245763 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1410186702539329 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (140094889551191353099 / 1000000000000000000000 : ℝ)) -
          6 * (2 * (1221993650998643614353 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (318180245763 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (318180245763 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (318180245763 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_52 :
    ((203275770246830504773 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(36435012247301481743849 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1433024399286347 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1423334185029087098537 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (150677267173378803647 / 625000000000000000000 : ℝ))))) ≤
      Vfield (41071178579 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (41071178579 / 2000000000000 : ℝ)) =
      Real.log (2041071178579 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((41071178579 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (52321178579 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (203275770246830504773 / 10000000000000000000000 : ℝ) ≤
      Real.log (2041071178579 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (52321178579 / 2000000000000 : ℝ) ≤
      (-(36435012247301481743849 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (52321178579 / 2000000000000 : ℝ) = (52321178579 / 31250000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (52321178579 / 31250000000 : ℝ) ≤
            (5153818570698518256151 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1433024399286347 / 10000000000000000 : ℝ) ≤ Real.sqrt (41071178579 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (41071178579 / 2000000000000 : ℝ) ≤ (28660487985727 / 200000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (41071178579 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau112 :
    Real.arctan (28660487985727 / 200000000000000 : ℝ) ≤
      (1423334185029087098537 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1423334185029087098537 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (200000000000000 / 28660487985727 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 28660487985727 : ℝ) =
              (28660487985727 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau112)
  have hz1 :
    (200000000000000 / 28660487985727 : ℝ) ≤ 1 / Real.sqrt (41071178579 / 2000000000000 : ℝ) := by
    rw [show (200000000000000 / 28660487985727 : ℝ) = 1 / (28660487985727 / 200000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau113 :
    Real.arctan (312500000000000000000000000000 / 1271019977433822553363219150469 : ℝ) ≤
      (150677267173378803647 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1433024399286347 : ℝ) ≤
      (2 * (150677267173378803647 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1410847878235981 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1433024399286347 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1433024399286347 : ℝ) /
                (1 + (1410847878235981 / 1250000000000000 : ℝ)) =
              (312500000000000000000000000000 / 1271019977433822553363219150469 : ℝ)
            by
        norm_num];
        exact hau113)
  have hz2 :
    (3 / 40) / Real.sqrt (41071178579 / 2000000000000 : ℝ) ≤
      (750000000000000 / 1433024399286347 : ℝ) := by
    rw [show
        (750000000000000 / 1433024399286347 : ℝ) =
          (3 / 40) / (1433024399286347 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1423334185029087098537 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (150677267173378803647 / 625000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (41071178579 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (41071178579 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1433024399286347 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1423334185029087098537 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (150677267173378803647 / 625000000000000000000 : ℝ)))) ≤
      Real.sqrt (41071178579 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (41071178579 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (41071178579 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_53 :
    ((107996420276222433859 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(35950526579446718972183 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1477641267294771 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (146702560506701594711 / 1000000000000000000000 : ℝ)) -
              6 * (2 * (2348409106350313720017 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (34934779437 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (34934779437 / 1600000000000 : ℝ)) =
      Real.log (1634934779437 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((34934779437 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (43934779437 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (107996420276222433859 / 5000000000000000000000 : ℝ) ≤
      Real.log (1634934779437 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (43934779437 / 1600000000000 : ℝ) ≤
      (-(35950526579446718972183 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (43934779437 / 1600000000000 : ℝ) = (43934779437 / 25000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43934779437 / 25000000000 : ℝ) ≤
            (5638304238553281027817 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1477641267294771 / 10000000000000000 : ℝ) ≤ Real.sqrt (34934779437 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (34934779437 / 1600000000000 : ℝ) ≤ (738820633647387 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (34934779437 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau114 :
    Real.arctan (738820633647387 / 5000000000000000 : ℝ) ≤
      (146702560506701594711 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (146702560506701594711 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 738820633647387 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 738820633647387 : ℝ) =
              (738820633647387 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau114)
  have hz1 :
    (5000000000000000 / 738820633647387 : ℝ) ≤ 1 / Real.sqrt (34934779437 / 1600000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 738820633647387 : ℝ) = 1 / (738820633647387 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau115 :
    Real.arctan (1250000000000000000000000000000 / 5224540267429134358032754116807 : ℝ) ≤
      (2348409106350313720017 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 492547089098257 : ℝ) ≤
      (2 * (2348409106350313720017 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5607189410040151 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (250000000000000 / 492547089098257 : ℝ) ^ 2))
      (by
        rw [show
            (250000000000000 / 492547089098257 : ℝ) /
                (1 + (5607189410040151 / 5000000000000000 : ℝ)) =
              (1250000000000000000000000000000 / 5224540267429134358032754116807 : ℝ)
            by
        norm_num];
        exact hau115)
  have hz2 :
    (3 / 40) / Real.sqrt (34934779437 / 1600000000000 : ℝ) ≤
      (250000000000000 / 492547089098257 : ℝ) := by
    rw [show
        (250000000000000 / 492547089098257 : ℝ) =
          (3 / 40) / (1477641267294771 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (146702560506701594711 / 1000000000000000000000 : ℝ)) -
        6 * (2 * (2348409106350313720017 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (34934779437 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (34934779437 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1477641267294771 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (146702560506701594711 / 1000000000000000000000 : ℝ)) -
          6 * (2 * (2348409106350313720017 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (34934779437 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (34934779437 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (34934779437 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_54 :
    ((114346879504294972067 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(35488432866774594506247 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1520949867903277 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1509382020844949857689 / 10000000000000000000000 : ℝ)) -
              6 * (4581227649370826993687 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (92531540027 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (92531540027 / 4000000000000 : ℝ)) =
      Real.log (4092531540027 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((92531540027 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (115031540027 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (114346879504294972067 / 5000000000000000000000 : ℝ) ≤
      Real.log (4092531540027 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (115031540027 / 4000000000000 : ℝ) ≤
      (-(35488432866774594506247 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (115031540027 / 4000000000000 : ℝ) = (115031540027 / 62500000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115031540027 / 62500000000 : ℝ) ≤
            (6100397951225405493753 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1520949867903277 / 10000000000000000 : ℝ) ≤ Real.sqrt (92531540027 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (92531540027 / 4000000000000 : ℝ) ≤ (19011873348791 / 125000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (92531540027 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau116 :
    Real.arctan (19011873348791 / 125000000000000 : ℝ) ≤
      (1509382020844949857689 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1509382020844949857689 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (125000000000000 / 19011873348791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 19011873348791 : ℝ) =
              (19011873348791 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hau116)
  have hz1 :
    (125000000000000 / 19011873348791 : ℝ) ≤ 1 / Real.sqrt (92531540027 / 4000000000000 : ℝ) := by
    rw [show (125000000000000 / 19011873348791 : ℝ) = 1 / (19011873348791 / 125000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1520949867903277 : ℝ) ≤
      (4581227649370826993687 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (92531540027 / 4000000000000 : ℝ) ≤
      (750000000000000 / 1520949867903277 : ℝ) := by
    rw [show
        (750000000000000 / 1520949867903277 : ℝ) =
          (3 / 40) / (1520949867903277 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1509382020844949857689 / 10000000000000000000000 : ℝ)) -
        6 * (4581227649370826993687 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (92531540027 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (92531540027 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1520949867903277 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1509382020844949857689 / 10000000000000000000000 : ℝ)) -
          6 * (4581227649370826993687 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (92531540027 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (92531540027 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (92531540027 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_55 :
    ((127023652061630830299 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(34623757699024104622901 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((40101574722821 / 250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1590513943220726835857 / 10000000000000000000000 : ℝ)) -
              6 * (218681344812415938491 / 500000000000000000000 : ℝ)))) ≤
      Vfield (6432545181 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6432545181 / 250000000000 : ℝ)) = Real.log (256432545181 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6432545181 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7838795181 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (127023652061630830299 / 5000000000000000000000 : ℝ) ≤
      Real.log (256432545181 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7838795181 / 250000000000 : ℝ) ≤
      (-(34623757699024104622901 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (7838795181 / 250000000000 : ℝ) = (7838795181 / 7812500000 : ℝ) / 2 ^ 5 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7838795181 / 7812500000 : ℝ) ≤
            (33601315975895377099 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (40101574722821 / 250000000000000 : ℝ) ≤ Real.sqrt (6432545181 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6432545181 / 250000000000 : ℝ) ≤ (1604062988912843 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6432545181 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau117 :
    Real.arctan (1604062988912843 / 10000000000000000 : ℝ) ≤
      (1590513943220726835857 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1590513943220726835857 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1604062988912843 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1604062988912843 : ℝ) =
              (1604062988912843 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau117)
  have hz1 :
    (10000000000000000 / 1604062988912843 : ℝ) ≤ 1 / Real.sqrt (6432545181 / 250000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1604062988912843 : ℝ) =
          1 / (1604062988912843 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (18750000000000 / 40101574722821 : ℝ) ≤
      (218681344812415938491 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6432545181 / 250000000000 : ℝ) ≤
      (18750000000000 / 40101574722821 : ℝ) := by
    rw [show
        (18750000000000 / 40101574722821 : ℝ) = (3 / 40) / (40101574722821 / 250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1590513943220726835857 / 10000000000000000000000 : ℝ)) -
        6 * (218681344812415938491 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6432545181 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6432545181 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((40101574722821 / 250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1590513943220726835857 / 10000000000000000000000 : ℝ)) -
          6 * (218681344812415938491 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (6432545181 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6432545181 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6432545181 / 250000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_56 :
    ((32987613906975619173 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(34306346441541073575049 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1635279580656621 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (324186506259879103831 / 2000000000000000000000 : ℝ)) -
              6 * (1075033352401525906013 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (213931144553 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (213931144553 / 8000000000000 : ℝ)) =
      Real.log (8213931144553 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((213931144553 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (258931144553 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (32987613906975619173 / 1250000000000000000000 : ℝ) ≤
      Real.log (8213931144553 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (258931144553 / 8000000000000 : ℝ) ≤
      (-(34306346441541073575049 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (258931144553 / 8000000000000 : ℝ) = (258931144553 / 250000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (258931144553 / 250000000000 : ℝ) ≤
            (351012573458926424951 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1635279580656621 / 10000000000000000 : ℝ) ≤ Real.sqrt (213931144553 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (213931144553 / 8000000000000 : ℝ) ≤ (102204973791039 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (213931144553 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau118 :
    Real.arctan (102204973791039 / 625000000000000 : ℝ) ≤
      (324186506259879103831 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (324186506259879103831 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 102204973791039 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 102204973791039 : ℝ) =
              (102204973791039 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau118)
  have hz1 :
    (625000000000000 / 102204973791039 : ℝ) ≤ 1 / Real.sqrt (213931144553 / 8000000000000 : ℝ) := by
    rw [show (625000000000000 / 102204973791039 : ℝ) = 1 / (102204973791039 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 545093193552207 : ℝ) ≤
      (1075033352401525906013 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (213931144553 / 8000000000000 : ℝ) ≤
      (250000000000000 / 545093193552207 : ℝ) := by
    rw [show
        (250000000000000 / 545093193552207 : ℝ) =
          (3 / 40) / (1635279580656621 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (324186506259879103831 / 2000000000000000000000 : ℝ)) -
        6 * (1075033352401525906013 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (213931144553 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (213931144553 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1635279580656621 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (324186506259879103831 / 2000000000000000000000 : ℝ)) -
          6 * (1075033352401525906013 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (213931144553 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (213931144553 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (213931144553 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_57 :
    ((13441203810162759651 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17075670345849735943963 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1650666509071031 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (817957512773989300277 / 5000000000000000000000 : ℝ)) -
              6 * (2132376865167301685317 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (435951987867 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (435951987867 / 16000000000000 : ℝ)) =
      Real.log (16435951987867 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((435951987867 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (525951987867 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (13441203810162759651 / 500000000000000000000 : ℝ) ≤
      Real.log (16435951987867 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (525951987867 / 16000000000000 : ℝ) ≤
      (-(17075670345849735943963 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (525951987867 / 16000000000000 : ℝ) = (525951987867 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (525951987867 / 500000000000 : ℝ) ≤
            (253009161650264056037 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1650666509071031 / 10000000000000000 : ℝ) ≤ Real.sqrt (435951987867 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (435951987867 / 16000000000000 : ℝ) ≤ (825333254535517 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (435951987867 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau119 :
    Real.arctan (825333254535517 / 5000000000000000 : ℝ) ≤
      (817957512773989300277 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (817957512773989300277 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 825333254535517 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 825333254535517 : ℝ) =
              (825333254535517 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau119)
  have hz1 :
    (5000000000000000 / 825333254535517 : ℝ) ≤
      1 / Real.sqrt (435951987867 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 825333254535517 : ℝ) = 1 / (825333254535517 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1650666509071031 : ℝ) ≤
      (2132376865167301685317 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (435951987867 / 16000000000000 : ℝ) ≤
      (750000000000000 / 1650666509071031 : ℝ) := by
    rw [show
        (750000000000000 / 1650666509071031 : ℝ) =
          (3 / 40) / (1650666509071031 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (817957512773989300277 / 5000000000000000000000 : ℝ)) -
        6 * (2132376865167301685317 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (435951987867 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (435951987867 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1650666509071031 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (817957512773989300277 / 5000000000000000000000 : ℝ)) -
          6 * (2132376865167301685317 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (435951987867 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (435951987867 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (435951987867 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_58 :
    ((34218102323501764669 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33998700991624565113719 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((83295566229917 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (66030073509107242779 / 400000000000000000000 : ℝ)) -
              6 * (846047177419245798601 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (111010421657 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (111010421657 / 4000000000000 : ℝ)) =
      Real.log (4111010421657 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((111010421657 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (133510421657 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (34218102323501764669 / 1250000000000000000000 : ℝ) ≤
      Real.log (4111010421657 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (133510421657 / 4000000000000 : ℝ) ≤
      (-(33998700991624565113719 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (133510421657 / 4000000000000 : ℝ) = (133510421657 / 125000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (133510421657 / 125000000000 : ℝ) ≤
            (658658023375434886281 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (83295566229917 / 500000000000000 : ℝ) ≤ Real.sqrt (111010421657 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (111010421657 / 4000000000000 : ℝ) ≤ (1665911324598343 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (111010421657 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau120 :
    Real.arctan (1665911324598343 / 10000000000000000 : ℝ) ≤
      (66030073509107242779 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (66030073509107242779 / 400000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1665911324598343 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1665911324598343 : ℝ) =
              (1665911324598343 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau120)
  have hz1 :
    (10000000000000000 / 1665911324598343 : ℝ) ≤
      1 / Real.sqrt (111010421657 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1665911324598343 : ℝ) =
          1 / (1665911324598343 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (37500000000000 / 83295566229917 : ℝ) ≤
      (846047177419245798601 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (111010421657 / 4000000000000 : ℝ) ≤
      (37500000000000 / 83295566229917 : ℝ) := by
    rw [show
        (37500000000000 / 83295566229917 : ℝ) = (3 / 40) / (83295566229917 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (66030073509107242779 / 400000000000000000000 : ℝ)) -
        6 * (846047177419245798601 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (111010421657 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (111010421657 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((83295566229917 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (66030073509107242779 / 400000000000000000000 : ℝ)) -
          6 * (846047177419245798601 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (111010421657 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (111010421657 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (111010421657 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_59 :
    ((27866314079307059799 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33848356193919409894199 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((42025447340579 / 250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (208180859025354406709 / 1250000000000000000000 : ℝ)) -
              6 * (4196545340860832545349 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (452131385389 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (452131385389 / 16000000000000 : ℝ)) =
      Real.log (16452131385389 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((452131385389 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (542131385389 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (27866314079307059799 / 1000000000000000000000 : ℝ) ≤
      Real.log (16452131385389 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (542131385389 / 16000000000000 : ℝ) ≤
      (-(33848356193919409894199 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (542131385389 / 16000000000000 : ℝ) = (542131385389 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (542131385389 / 500000000000 : ℝ) ≤
            (809002821080590105801 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (42025447340579 / 250000000000000 : ℝ) ≤ Real.sqrt (452131385389 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (452131385389 / 16000000000000 : ℝ) ≤ (1681017893623163 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (452131385389 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau121 :
    Real.arctan (1681017893623163 / 10000000000000000 : ℝ) ≤
      (208180859025354406709 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (208180859025354406709 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1681017893623163 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1681017893623163 : ℝ) =
              (1681017893623163 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau121)
  have hz1 :
    (10000000000000000 / 1681017893623163 : ℝ) ≤
      1 / Real.sqrt (452131385389 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1681017893623163 : ℝ) =
          1 / (1681017893623163 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (18750000000000 / 42025447340579 : ℝ) ≤
      (4196545340860832545349 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (452131385389 / 16000000000000 : ℝ) ≤
      (18750000000000 / 42025447340579 : ℝ) := by
    rw [show
        (18750000000000 / 42025447340579 : ℝ) = (3 / 40) / (42025447340579 / 250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (208180859025354406709 / 1250000000000000000000 : ℝ)) -
        6 * (4196545340860832545349 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (452131385389 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (452131385389 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((42025447340579 / 250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (208180859025354406709 / 1250000000000000000000 : ℝ)) -
          6 * (4196545340860832545349 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (452131385389 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (452131385389 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (452131385389 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_60 :
    ((4392521797998957757 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33774023019545920101553 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((844260248280909 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (418185598816008147827 / 2500000000000000000000 : ℝ)) -
              6 * (1045000009396149589471 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (912352469539 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (912352469539 / 32000000000000 : ℝ)) =
      Real.log (32912352469539 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((912352469539 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1092352469539 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4392521797998957757 / 156250000000000000000 : ℝ) ≤
      Real.log (32912352469539 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1092352469539 / 32000000000000 : ℝ) ≤
      (-(33774023019545920101553 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1092352469539 / 32000000000000 : ℝ) = (1092352469539 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1092352469539 / 1000000000000 : ℝ) ≤
            (883335995454079898447 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (844260248280909 / 5000000000000000 : ℝ) ≤ Real.sqrt (912352469539 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (912352469539 / 32000000000000 : ℝ) ≤ (1688520496561821 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (912352469539 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau122 :
    Real.arctan (1688520496561821 / 10000000000000000 : ℝ) ≤
      (418185598816008147827 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (418185598816008147827 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1688520496561821 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1688520496561821 : ℝ) =
              (1688520496561821 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau122)
  have hz1 :
    (10000000000000000 / 1688520496561821 : ℝ) ≤
      1 / Real.sqrt (912352469539 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1688520496561821 : ℝ) =
          1 / (1688520496561821 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 281420082760303 : ℝ) ≤
      (1045000009396149589471 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (912352469539 / 32000000000000 : ℝ) ≤
      (125000000000000 / 281420082760303 : ℝ) := by
    rw [show
        (125000000000000 / 281420082760303 : ℝ) =
          (3 / 40) / (844260248280909 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (418185598816008147827 / 2500000000000000000000 : ℝ)) -
        6 * (1045000009396149589471 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (912352469539 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (912352469539 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((844260248280909 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (418185598816008147827 / 2500000000000000000000 : ℝ)) -
          6 * (1045000009396149589471 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (912352469539 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (912352469539 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (912352469539 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
