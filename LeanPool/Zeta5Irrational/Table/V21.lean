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

/-! # V21: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_253 :
    ((243944585903856897783 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3018052558963085022733 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((580274971356627 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4346161340798394868929 / 10000000000000000000000 : ℝ)) -
              6 * (100110784012609814337 / 625000000000000000000 : ℝ)))) ≤
      Vfield (2758402395201 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2758402395201 / 12800000000000 : ℝ)) =
      Real.log (15558402395201 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2758402395201 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2830402395201 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (243944585903856897783 / 1250000000000000000000 : ℝ) ≤
      Real.log (15558402395201 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2830402395201 / 12800000000000 : ℝ) ≤
      (-(3018052558963085022733 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2830402395201 / 12800000000000 : ℝ) = (2830402395201 / 1600000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2830402395201 / 1600000000000 : ℝ) ≤
            (1140830522836914977267 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (580274971356627 / 1250000000000000 : ℝ) ≤ Real.sqrt (2758402395201 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2758402395201 / 12800000000000 : ℝ) ≤ (4642199770853019 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2758402395201 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau315 :
    Real.arctan (4642199770853019 / 10000000000000000 : ℝ) ≤
      (4346161340798394868929 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4346161340798394868929 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4642199770853019 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4642199770853019 : ℝ) =
              (4642199770853019 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau315)
  have hz1 :
    (10000000000000000 / 4642199770853019 : ℝ) ≤
      1 / Real.sqrt (2758402395201 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4642199770853019 : ℝ) =
          1 / (4642199770853019 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 193424990452209 : ℝ) ≤
      (100110784012609814337 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2758402395201 / 12800000000000 : ℝ) ≤
      (31250000000000 / 193424990452209 : ℝ) := by
    rw [show
        (31250000000000 / 193424990452209 : ℝ) =
          (3 / 40) / (580274971356627 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4346161340798394868929 / 10000000000000000000000 : ℝ)) -
        6 * (100110784012609814337 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2758402395201 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2758402395201 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((580274971356627 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4346161340798394868929 / 10000000000000000000000 : ℝ)) -
          6 * (100110784012609814337 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (2758402395201 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2758402395201 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2758402395201 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_254 :
    ((488985448782286927153 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15066182083325074857749 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2323969201358757 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4350881516122305889661 / 10000000000000000000000 : ℝ)) -
              6 * (1599828489360179180629 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3456533023273 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3456533023273 / 16000000000000 : ℝ)) =
      Real.log (19456533023273 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3456533023273 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3546533023273 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (488985448782286927153 / 2500000000000000000000 : ℝ) ≤
      Real.log (19456533023273 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3546533023273 / 16000000000000 : ℝ) ≤
      (-(15066182083325074857749 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3546533023273 / 16000000000000 : ℝ) = (3546533023273 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3546533023273 / 2000000000000 : ℝ) ≤
            (5728233325674925142251 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2323969201358757 / 5000000000000000 : ℝ) ≤ Real.sqrt (3456533023273 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3456533023273 / 16000000000000 : ℝ) ≤ (4647938402717517 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3456533023273 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau316 :
    Real.arctan (4647938402717517 / 10000000000000000 : ℝ) ≤
      (4350881516122305889661 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4350881516122305889661 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4647938402717517 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4647938402717517 : ℝ) =
              (4647938402717517 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau316)
  have hz1 :
    (10000000000000000 / 4647938402717517 : ℝ) ≤
      1 / Real.sqrt (3456533023273 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4647938402717517 : ℝ) =
          1 / (4647938402717517 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 774656400452919 : ℝ) ≤
      (1599828489360179180629 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3456533023273 / 16000000000000 : ℝ) ≤
      (125000000000000 / 774656400452919 : ℝ) := by
    rw [show
        (125000000000000 / 774656400452919 : ℝ) =
          (3 / 40) / (2323969201358757 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4350881516122305889661 / 10000000000000000000000 : ℝ)) -
        6 * (1599828489360179180629 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3456533023273 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3456533023273 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2323969201358757 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4350881516122305889661 / 10000000000000000000000 : ℝ)) -
          6 * (1599828489360179180629 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3456533023273 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3456533023273 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3456533023273 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_255 :
    ((1960324980953131803927 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1504215922062519674107 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((290854372377773 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (544449225552295190347 / 1250000000000000000000 : ℝ)) -
              6 * (1597891496232632013767 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (13860252210179 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (13860252210179 / 64000000000000 : ℝ)) =
      Real.log (77860252210179 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((13860252210179 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14220252210179 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1960324980953131803927 / 10000000000000000000000 : ℝ) ≤
      Real.log (77860252210179 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14220252210179 / 64000000000000 : ℝ) ≤
      (-(1504215922062519674107 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14220252210179 / 64000000000000 : ℝ) = (14220252210179 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14220252210179 / 8000000000000 : ℝ) ≤
            (575225618837480325893 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (290854372377773 / 625000000000000 : ℝ) ≤ Real.sqrt (13860252210179 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (13860252210179 / 64000000000000 : ℝ) ≤
      (4653669958044371 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (13860252210179 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau317 :
    Real.arctan (4653669958044371 / 10000000000000000 : ℝ) ≤
      (544449225552295190347 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (544449225552295190347 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4653669958044371 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4653669958044371 : ℝ) =
              (4653669958044371 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau317)
  have hz1 :
    (10000000000000000 / 4653669958044371 : ℝ) ≤
      1 / Real.sqrt (13860252210179 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4653669958044371 : ℝ) =
          1 / (4653669958044371 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 290854372377773 : ℝ) ≤
      (1597891496232632013767 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (13860252210179 / 64000000000000 : ℝ) ≤
      (46875000000000 / 290854372377773 : ℝ) := by
    rw [show
        (46875000000000 / 290854372377773 : ℝ) =
          (3 / 40) / (290854372377773 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (544449225552295190347 / 1250000000000000000000 : ℝ)) -
        6 * (1597891496232632013767 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (13860252210179 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (13860252210179 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((290854372377773 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (544449225552295190347 / 1250000000000000000000 : ℝ)) -
          6 * (1597891496232632013767 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (13860252210179 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (13860252210179 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (13860252210179 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_256 :
    ((982353123193515533941 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7509096964721451375789 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2329697231474141 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (872059646811761308523 / 2000000000000000000000 : ℝ)) -
              6 * (1595961522167481885227 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (6947186163633 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6947186163633 / 32000000000000 : ℝ)) =
      Real.log (38947186163633 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6947186163633 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7127186163633 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (982353123193515533941 / 5000000000000000000000 : ℝ) ≤
      Real.log (38947186163633 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7127186163633 / 32000000000000 : ℝ) ≤
      (-(7509096964721451375789 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7127186163633 / 32000000000000 : ℝ) = (7127186163633 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7127186163633 / 4000000000000 : ℝ) ≤
            (2888110739778548624211 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2329697231474141 / 5000000000000000 : ℝ) ≤ Real.sqrt (6947186163633 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6947186163633 / 32000000000000 : ℝ) ≤ (931878892589657 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6947186163633 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau318 :
    Real.arctan (931878892589657 / 2000000000000000 : ℝ) ≤
      (872059646811761308523 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (872059646811761308523 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 931878892589657 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 931878892589657 : ℝ) =
              (931878892589657 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau318)
  have hz1 :
    (2000000000000000 / 931878892589657 : ℝ) ≤
      1 / Real.sqrt (6947186163633 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 931878892589657 : ℝ) = 1 / (931878892589657 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2329697231474141 : ℝ) ≤
      (1595961522167481885227 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6947186163633 / 32000000000000 : ℝ) ≤
      (375000000000000 / 2329697231474141 : ℝ) := by
    rw [show
        (375000000000000 / 2329697231474141 : ℝ) =
          (3 / 40) / (2329697231474141 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (872059646811761308523 / 2000000000000000000000 : ℝ)) -
        6 * (1595961522167481885227 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6947186163633 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6947186163633 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2329697231474141 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (872059646811761308523 / 2000000000000000000000 : ℝ)) -
          6 * (1595961522167481885227 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (6947186163633 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6947186163633 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6947186163633 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_257 :
    ((246135699139107045039 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14994285934494019374537 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4665111943383733 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (17459979332987969381 / 40000000000000000000 : ℝ)) -
              6 * (398509631218225111797 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (13928492444353 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (13928492444353 / 64000000000000 : ℝ)) =
      Real.log (77928492444353 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((13928492444353 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14288492444353 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (246135699139107045039 / 1250000000000000000000 : ℝ) ≤
      Real.log (77928492444353 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14288492444353 / 64000000000000 : ℝ) ≤
      (-(14994285934494019374537 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14288492444353 / 64000000000000 : ℝ) = (14288492444353 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14288492444353 / 8000000000000 : ℝ) ≤
            (5800129474505980625463 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4665111943383733 / 10000000000000000 : ℝ) ≤
      Real.sqrt (13928492444353 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (13928492444353 / 64000000000000 : ℝ) ≤ (583138992922967 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (13928492444353 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau319 :
    Real.arctan (583138992922967 / 1250000000000000 : ℝ) ≤
      (17459979332987969381 / 40000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (17459979332987969381 / 40000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 583138992922967 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 583138992922967 : ℝ) =
              (583138992922967 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau319)
  have hz1 :
    (1250000000000000 / 583138992922967 : ℝ) ≤
      1 / Real.sqrt (13928492444353 / 64000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 583138992922967 : ℝ) = 1 / (583138992922967 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4665111943383733 : ℝ) ≤
      (398509631218225111797 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (13928492444353 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4665111943383733 : ℝ) := by
    rw [show
        (750000000000000 / 4665111943383733 : ℝ) =
          (3 / 40) / (4665111943383733 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (17459979332987969381 / 40000000000000000000 : ℝ)) -
        6 * (398509631218225111797 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (13928492444353 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (13928492444353 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4665111943383733 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (17459979332987969381 / 40000000000000000000 : ℝ)) -
          6 * (398509631218225111797 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (13928492444353 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (13928492444353 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (13928492444353 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_258 :
    ((1973463022810409675657 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14970434962464114446783 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((934164485029269 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2184841815009400424567 / 5000000000000000000000 : ℝ)) -
              6 * (796061231206485465923 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (87266328509 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (87266328509 / 400000000000 : ℝ)) =
      Real.log (487266328509 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((87266328509 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (89516328509 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1973463022810409675657 / 10000000000000000000000 : ℝ) ≤
      Real.log (487266328509 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (89516328509 / 400000000000 : ℝ) ≤
      (-(14970434962464114446783 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (89516328509 / 400000000000 : ℝ) = (89516328509 / 50000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (89516328509 / 50000000000 : ℝ) ≤
            (5823980446535885553217 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (934164485029269 / 2000000000000000 : ℝ) ≤ Real.sqrt (87266328509 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (87266328509 / 400000000000 : ℝ) ≤ (1167705606286587 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (87266328509 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau320 :
    Real.arctan (1167705606286587 / 2500000000000000 : ℝ) ≤
      (2184841815009400424567 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2184841815009400424567 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1167705606286587 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1167705606286587 : ℝ) =
              (1167705606286587 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau320)
  have hz1 :
    (2500000000000000 / 1167705606286587 : ℝ) ≤ 1 / Real.sqrt (87266328509 / 400000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1167705606286587 : ℝ) = 1 / (1167705606286587 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 311388161676423 : ℝ) ≤
      (796061231206485465923 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (87266328509 / 400000000000 : ℝ) ≤
      (50000000000000 / 311388161676423 : ℝ) := by
    rw [show
        (50000000000000 / 311388161676423 : ℝ) =
          (3 / 40) / (934164485029269 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2184841815009400424567 / 5000000000000000000000 : ℝ)) -
        6 * (796061231206485465923 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (87266328509 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (87266328509 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((934164485029269 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2184841815009400424567 / 5000000000000000000000 : ℝ)) -
          6 * (796061231206485465923 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (87266328509 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (87266328509 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (87266328509 / 400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_259 :
    ((395567707431457601787 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1868330092748718717143 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((18706103735497 / 40000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (109359116306101365259 / 250000000000000000000 : ℝ)) -
              6 * (1590213293203845113049 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (13996732678527 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (13996732678527 / 64000000000000 : ℝ)) =
      Real.log (77996732678527 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((13996732678527 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14356732678527 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (395567707431457601787 / 2000000000000000000000 : ℝ) ≤
      Real.log (77996732678527 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14356732678527 / 64000000000000 : ℝ) ≤
      (-(1868330092748718717143 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14356732678527 / 64000000000000 : ℝ) = (14356732678527 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14356732678527 / 8000000000000 : ℝ) ≤
            (730971833376281282857 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (18706103735497 / 40000000000000 : ℝ) ≤ Real.sqrt (13996732678527 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (13996732678527 / 64000000000000 : ℝ) ≤
      (4676525933874253 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (13996732678527 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau321 :
    Real.arctan (4676525933874253 / 10000000000000000 : ℝ) ≤
      (109359116306101365259 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (109359116306101365259 / 250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4676525933874253 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4676525933874253 : ℝ) =
              (4676525933874253 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau321)
  have hz1 :
    (10000000000000000 / 4676525933874253 : ℝ) ≤
      1 / Real.sqrt (13996732678527 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4676525933874253 : ℝ) =
          1 / (4676525933874253 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (3000000000000 / 18706103735497 : ℝ) ≤
      (1590213293203845113049 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (13996732678527 / 64000000000000 : ℝ) ≤
      (3000000000000 / 18706103735497 : ℝ) := by
    rw [show
        (3000000000000 / 18706103735497 : ℝ) = (3 / 40) / (18706103735497 / 40000000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (109359116306101365259 / 250000000000000000000 : ℝ)) -
        6 * (1590213293203845113049 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (13996732678527 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (13996732678527 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((18706103735497 / 40000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (109359116306101365259 / 250000000000000000000 : ℝ)) -
          6 * (1590213293203845113049 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (13996732678527 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (13996732678527 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (13996732678527 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_260 :
    ((1982212137828887213253 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7461451501819978019017 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((187288899801977 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2189518963813952082979 / 5000000000000000000000 : ℝ)) -
              6 * (1588310976009953894083 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7015426397807 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7015426397807 / 32000000000000 : ℝ)) =
      Real.log (39015426397807 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7015426397807 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7195426397807 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1982212137828887213253 / 10000000000000000000000 : ℝ) ≤
      Real.log (39015426397807 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7195426397807 / 32000000000000 : ℝ) ≤
      (-(7461451501819978019017 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7195426397807 / 32000000000000 : ℝ) = (7195426397807 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7195426397807 / 4000000000000 : ℝ) ≤
            (2935756202680021980983 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (187288899801977 / 400000000000000 : ℝ) ≤ Real.sqrt (7015426397807 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7015426397807 / 32000000000000 : ℝ) ≤ (1170555623762357 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7015426397807 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau322 :
    Real.arctan (1170555623762357 / 2500000000000000 : ℝ) ≤
      (2189518963813952082979 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2189518963813952082979 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1170555623762357 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1170555623762357 : ℝ) =
              (1170555623762357 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau322)
  have hz1 :
    (2500000000000000 / 1170555623762357 : ℝ) ≤
      1 / Real.sqrt (7015426397807 / 32000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1170555623762357 : ℝ) = 1 / (1170555623762357 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (30000000000000 / 187288899801977 : ℝ) ≤
      (1588310976009953894083 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7015426397807 / 32000000000000 : ℝ) ≤
      (30000000000000 / 187288899801977 : ℝ) := by
    rw [show
        (30000000000000 / 187288899801977 : ℝ) =
          (3 / 40) / (187288899801977 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2189518963813952082979 / 5000000000000000000000 : ℝ)) -
        6 * (1588310976009953894083 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7015426397807 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7015426397807 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((187288899801977 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2189518963813952082979 / 5000000000000000000000 : ℝ)) -
          6 * (1588310976009953894083 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7015426397807 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7015426397807 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7015426397807 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_261 :
    ((198658382649840584889 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7449610739948963803307 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2343956066999513 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (219185174185610494233 / 500000000000000000000 : ℝ)) -
              6 * (1586415469940263764489 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (14064972912701 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14064972912701 / 64000000000000 : ℝ)) =
      Real.log (78064972912701 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14064972912701 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14424972912701 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (198658382649840584889 / 1000000000000000000000 : ℝ) ≤
      Real.log (78064972912701 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14424972912701 / 64000000000000 : ℝ) ≤
      (-(7449610739948963803307 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14424972912701 / 64000000000000 : ℝ) = (14424972912701 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14424972912701 / 8000000000000 : ℝ) ≤
            (2947596964551036196693 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2343956066999513 / 5000000000000000 : ℝ) ≤ Real.sqrt (14064972912701 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14064972912701 / 64000000000000 : ℝ) ≤
      (4687912133999029 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14064972912701 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau323 :
    Real.arctan (4687912133999029 / 10000000000000000 : ℝ) ≤
      (219185174185610494233 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (219185174185610494233 / 500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4687912133999029 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4687912133999029 : ℝ) =
              (4687912133999029 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau323)
  have hz1 :
    (10000000000000000 / 4687912133999029 : ℝ) ≤
      1 / Real.sqrt (14064972912701 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4687912133999029 : ℝ) =
          1 / (4687912133999029 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2343956066999513 : ℝ) ≤
      (1586415469940263764489 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (14064972912701 / 64000000000000 : ℝ) ≤
      (375000000000000 / 2343956066999513 : ℝ) := by
    rw [show
        (375000000000000 / 2343956066999513 : ℝ) =
          (3 / 40) / (2343956066999513 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (219185174185610494233 / 500000000000000000000 : ℝ)) -
        6 * (1586415469940263764489 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14064972912701 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14064972912701 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2343956066999513 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (219185174185610494233 / 500000000000000000000 : ℝ)) -
          6 * (1586415469940263764489 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (14064972912701 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14064972912701 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14064972912701 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_262 :
    ((248869200604606127997 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14875595905142932846117 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2346797437948349 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4388361347876901126497 / 10000000000000000000000 : ℝ)) -
              6 * (396131683611146364051 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (3524773257447 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3524773257447 / 16000000000000 : ℝ)) =
      Real.log (19524773257447 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3524773257447 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3614773257447 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (248869200604606127997 / 1250000000000000000000 : ℝ) ≤
      Real.log (19524773257447 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3614773257447 / 16000000000000 : ℝ) ≤
      (-(14875595905142932846117 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3614773257447 / 16000000000000 : ℝ) = (3614773257447 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3614773257447 / 2000000000000 : ℝ) ≤
            (5918819503857067153883 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2346797437948349 / 5000000000000000 : ℝ) ≤ Real.sqrt (3524773257447 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3524773257447 / 16000000000000 : ℝ) ≤ (4693594875896701 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3524773257447 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau324 :
    Real.arctan (4693594875896701 / 10000000000000000 : ℝ) ≤
      (4388361347876901126497 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4388361347876901126497 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4693594875896701 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4693594875896701 : ℝ) =
              (4693594875896701 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau324)
  have hz1 :
    (10000000000000000 / 4693594875896701 : ℝ) ≤
      1 / Real.sqrt (3524773257447 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4693594875896701 : ℝ) =
          1 / (4693594875896701 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2346797437948349 : ℝ) ≤
      (396131683611146364051 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3524773257447 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2346797437948349 : ℝ) := by
    rw [show
        (375000000000000 / 2346797437948349 : ℝ) =
          (3 / 40) / (2346797437948349 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4388361347876901126497 / 10000000000000000000000 : ℝ)) -
        6 * (396131683611146364051 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3524773257447 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3524773257447 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2346797437948349 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4388361347876901126497 / 10000000000000000000000 : ℝ)) -
          6 * (396131683611146364051 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (3524773257447 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3524773257447 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3524773257447 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_263 :
    ((1995321474513032226771 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14852026015632438169299 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1174817686440969 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1098252886835331265209 / 2500000000000000000000 : ℝ)) -
              6 * (1582644729309929085451 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4522628207 / 20480000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4522628207 / 20480000000 : ℝ)) = Real.log (25002628207 / 20480000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((4522628207 / 20480000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4637828207 / 20480000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1995321474513032226771 / 10000000000000000000000 : ℝ) ≤
      Real.log (25002628207 / 20480000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4637828207 / 20480000000 : ℝ) ≤
      (-(14852026015632438169299 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4637828207 / 20480000000 : ℝ) = (4637828207 / 2560000000 : ℝ) / 2 ^ 3 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4637828207 / 2560000000 : ℝ) ≤
            (5942389393367561830701 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1174817686440969 / 2500000000000000 : ℝ) ≤ Real.sqrt (4522628207 / 20480000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4522628207 / 20480000000 : ℝ) ≤ (4699270745763879 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4522628207 / 20480000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau325 :
    Real.arctan (4699270745763879 / 10000000000000000 : ℝ) ≤
      (1098252886835331265209 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1098252886835331265209 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4699270745763879 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4699270745763879 : ℝ) =
              (4699270745763879 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau325)
  have hz1 :
    (10000000000000000 / 4699270745763879 : ℝ) ≤ 1 / Real.sqrt (4522628207 / 20480000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4699270745763879 : ℝ) =
          1 / (4699270745763879 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 391605895480323 : ℝ) ≤
      (1582644729309929085451 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4522628207 / 20480000000 : ℝ) ≤
      (62500000000000 / 391605895480323 : ℝ) := by
    rw [show
        (62500000000000 / 391605895480323 : ℝ) =
          (3 / 40) / (1174817686440969 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1098252886835331265209 / 2500000000000000000000 : ℝ)) -
        6 * (1582644729309929085451 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4522628207 / 20480000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4522628207 / 20480000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1174817686440969 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1098252886835331265209 / 2500000000000000000000 : ℝ)) -
          6 * (1582644729309929085451 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4522628207 / 20480000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4522628207 / 20480000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4522628207 / 20480000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_264 :
    ((999843718596792574793 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14828511549484442036283 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4704939768471071 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4397654109165580255539 / 10000000000000000000000 : ℝ)) -
              6 * (158076941465690711107 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (7083666631981 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7083666631981 / 32000000000000 : ℝ)) =
      Real.log (39083666631981 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7083666631981 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7263666631981 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (999843718596792574793 / 5000000000000000000000 : ℝ) ≤
      Real.log (39083666631981 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7263666631981 / 32000000000000 : ℝ) ≤
      (-(14828511549484442036283 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7263666631981 / 32000000000000 : ℝ) = (7263666631981 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7263666631981 / 4000000000000 : ℝ) ≤
            (5965903859515557963717 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4704939768471071 / 10000000000000000 : ℝ) ≤ Real.sqrt (7083666631981 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7083666631981 / 32000000000000 : ℝ) ≤ (2352469884235537 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7083666631981 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau326 :
    Real.arctan (2352469884235537 / 5000000000000000 : ℝ) ≤
      (4397654109165580255539 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4397654109165580255539 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2352469884235537 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2352469884235537 : ℝ) =
              (2352469884235537 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau326)
  have hz1 :
    (5000000000000000 / 2352469884235537 : ℝ) ≤
      1 / Real.sqrt (7083666631981 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2352469884235537 : ℝ) = 1 / (2352469884235537 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4704939768471071 : ℝ) ≤
      (158076941465690711107 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7083666631981 / 32000000000000 : ℝ) ≤
      (750000000000000 / 4704939768471071 : ℝ) := by
    rw [show
        (750000000000000 / 4704939768471071 : ℝ) =
          (3 / 40) / (4704939768471071 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4397654109165580255539 / 10000000000000000000000 : ℝ)) -
        6 * (158076941465690711107 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7083666631981 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7083666631981 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4704939768471071 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4397654109165580255539 / 10000000000000000000000 : ℝ)) -
          6 * (158076941465690711107 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (7083666631981 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7083666631981 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7083666631981 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
