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

/-! # V08: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_97 :
    ((15510994756587233961 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14366454297200582094051 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2255829004820067 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1109345930554525236403 / 5000000000000000000000 : ℝ)) -
              6 * (1604875809082805327399 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (407101159919 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (407101159919 / 8000000000000 : ℝ)) =
      Real.log (8407101159919 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((407101159919 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (452101159919 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (15510994756587233961 / 312500000000000000000 : ℝ) ≤
      Real.log (8407101159919 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (452101159919 / 8000000000000 : ℝ) ≤
      (-(14366454297200582094051 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (452101159919 / 8000000000000 : ℝ) = (452101159919 / 250000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (452101159919 / 250000000000 : ℝ) ≤
            (2962225210299417905949 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2255829004820067 / 10000000000000000 : ℝ) ≤ Real.sqrt (407101159919 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (407101159919 / 8000000000000 : ℝ) ≤ (225582900482007 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (407101159919 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau159 :
    Real.arctan (225582900482007 / 1000000000000000 : ℝ) ≤
      (1109345930554525236403 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1109345930554525236403 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 225582900482007 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 225582900482007 : ℝ) =
              (225582900482007 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau159)
  have hz1 :
    (1000000000000000 / 225582900482007 : ℝ) ≤ 1 / Real.sqrt (407101159919 / 8000000000000 : ℝ) :=
  by
    rw [show
        (1000000000000000 / 225582900482007 : ℝ) = 1 / (225582900482007 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 751943001606689 : ℝ) ≤
      (1604875809082805327399 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (407101159919 / 8000000000000 : ℝ) ≤
      (250000000000000 / 751943001606689 : ℝ) := by
    rw [show
        (250000000000000 / 751943001606689 : ℝ) =
          (3 / 40) / (2255829004820067 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1109345930554525236403 / 5000000000000000000000 : ℝ)) -
        6 * (1604875809082805327399 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (407101159919 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (407101159919 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2255829004820067 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1109345930554525236403 / 5000000000000000000000 : ℝ)) -
          6 * (1604875809082805327399 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (407101159919 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (407101159919 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (407101159919 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_98 :
    ((503468730297146605923 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(28601387060477260572887 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1136175792060049 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (89376350887521459017 / 400000000000000000000 : ℝ)) -
              6 * (318796760635867034687 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (1652346150993 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1652346150993 / 32000000000000 : ℝ)) =
      Real.log (33652346150993 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1652346150993 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1832346150993 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (503468730297146605923 / 10000000000000000000000 : ℝ) ≤
      Real.log (33652346150993 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1832346150993 / 32000000000000 : ℝ) ≤
      (-(28601387060477260572887 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1832346150993 / 32000000000000 : ℝ) = (1832346150993 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1832346150993 / 1000000000000 : ℝ) ≤
            (6055971954522739427113 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1136175792060049 / 5000000000000000 : ℝ) ≤ Real.sqrt (1652346150993 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1652346150993 / 32000000000000 : ℝ) ≤ (2272351584120101 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1652346150993 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau160 :
    Real.arctan (2272351584120101 / 10000000000000000 : ℝ) ≤
      (89376350887521459017 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (89376350887521459017 / 400000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2272351584120101 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2272351584120101 : ℝ) =
              (2272351584120101 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau160)
  have hz1 :
    (10000000000000000 / 2272351584120101 : ℝ) ≤
      1 / Real.sqrt (1652346150993 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2272351584120101 : ℝ) =
          1 / (2272351584120101 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1136175792060049 : ℝ) ≤
      (318796760635867034687 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1652346150993 / 32000000000000 : ℝ) ≤
      (375000000000000 / 1136175792060049 : ℝ) := by
    rw [show
        (375000000000000 / 1136175792060049 : ℝ) =
          (3 / 40) / (1136175792060049 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (89376350887521459017 / 400000000000000000000 : ℝ)) -
        6 * (318796760635867034687 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1652346150993 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1652346150993 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1136175792060049 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (89376350887521459017 / 400000000000000000000 : ℝ)) -
          6 * (318796760635867034687 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (1652346150993 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1652346150993 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1652346150993 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_99 :
    ((510580566961623545383 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(28471572886770229474981 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((457750977922221 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2250001128422295373419 / 10000000000000000000000 : ℝ)) -
              6 * (1583310802186801713659 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (167628766231 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (167628766231 / 3200000000000 : ℝ)) =
      Real.log (3367628766231 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((167628766231 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (185628766231 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (510580566961623545383 / 10000000000000000000000 : ℝ) ≤
      Real.log (3367628766231 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (185628766231 / 3200000000000 : ℝ) ≤
      (-(28471572886770229474981 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (185628766231 / 3200000000000 : ℝ) = (185628766231 / 100000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (185628766231 / 100000000000 : ℝ) ≤
            (6185786128229770525019 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (457750977922221 / 2000000000000000 : ℝ) ≤ Real.sqrt (167628766231 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (167628766231 / 3200000000000 : ℝ) ≤ (572188722402777 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (167628766231 / 3200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau161 :
    Real.arctan (572188722402777 / 2500000000000000 : ℝ) ≤
      (2250001128422295373419 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2250001128422295373419 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 572188722402777 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 572188722402777 : ℝ) =
              (572188722402777 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau161)
  have hz1 :
    (2500000000000000 / 572188722402777 : ℝ) ≤ 1 / Real.sqrt (167628766231 / 3200000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 572188722402777 : ℝ) = 1 / (572188722402777 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 152583659307407 : ℝ) ≤
      (1583310802186801713659 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (167628766231 / 3200000000000 : ℝ) ≤
      (50000000000000 / 152583659307407 : ℝ) := by
    rw [show
        (50000000000000 / 152583659307407 : ℝ) =
          (3 / 40) / (457750977922221 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2250001128422295373419 / 10000000000000000000000 : ℝ)) -
        6 * (1583310802186801713659 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (167628766231 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (167628766231 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((457750977922221 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2250001128422295373419 / 10000000000000000000000 : ℝ)) -
          6 * (1583310802186801713659 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (167628766231 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (167628766231 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (167628766231 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_100 :
    ((6471091867478608207 / 125000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(28343422312220233724777 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((72032545864051 / 312500000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2265471525602191722833 / 10000000000000000000000 : ℝ)) -
              6 * (1572849557147011448877 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1700229173627 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1700229173627 / 32000000000000 : ℝ)) =
      Real.log (33700229173627 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1700229173627 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1880229173627 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (6471091867478608207 / 125000000000000000000 : ℝ) ≤
      Real.log (33700229173627 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1880229173627 / 32000000000000 : ℝ) ≤
      (-(28343422312220233724777 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1880229173627 / 32000000000000 : ℝ) = (1880229173627 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1880229173627 / 1000000000000 : ℝ) ≤
            (6313936702779766275223 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (72032545864051 / 312500000000000 : ℝ) ≤ Real.sqrt (1700229173627 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1700229173627 / 32000000000000 : ℝ) ≤ (461008293529927 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1700229173627 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau162 :
    Real.arctan (461008293529927 / 2000000000000000 : ℝ) ≤
      (2265471525602191722833 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2265471525602191722833 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 461008293529927 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 461008293529927 : ℝ) =
              (461008293529927 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau162)
  have hz1 :
    (2000000000000000 / 461008293529927 : ℝ) ≤
      1 / Real.sqrt (1700229173627 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 461008293529927 : ℝ) = 1 / (461008293529927 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (23437500000000 / 72032545864051 : ℝ) ≤
      (1572849557147011448877 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1700229173627 / 32000000000000 : ℝ) ≤
      (23437500000000 / 72032545864051 : ℝ) := by
    rw [show
        (23437500000000 / 72032545864051 : ℝ) = (3 / 40) / (72032545864051 / 312500000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2265471525602191722833 / 10000000000000000000000 : ℝ)) -
        6 * (1572849557147011448877 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1700229173627 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1700229173627 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((72032545864051 / 312500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2265471525602191722833 / 10000000000000000000000 : ℝ)) -
          6 * (1572849557147011448877 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1700229173627 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1700229173627 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1700229173627 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_101 :
    ((524789084785909236581 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(28216893236949584838917 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1160606887629269 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2280822469190898733897 / 10000000000000000000000 : ℝ)) -
              6 * (3125186301868497031861 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (107760667809 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (107760667809 / 2000000000000 : ℝ)) =
      Real.log (2107760667809 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((107760667809 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (119010667809 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (524789084785909236581 / 10000000000000000000000 : ℝ) ≤
      Real.log (2107760667809 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (119010667809 / 2000000000000 : ℝ) ≤
      (-(28216893236949584838917 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (119010667809 / 2000000000000 : ℝ) = (119010667809 / 62500000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (119010667809 / 62500000000 : ℝ) ≤
            (6440465778050415161083 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1160606887629269 / 5000000000000000 : ℝ) ≤ Real.sqrt (107760667809 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (107760667809 / 2000000000000 : ℝ) ≤ (2321213775258541 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (107760667809 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau163 :
    Real.arctan (2321213775258541 / 10000000000000000 : ℝ) ≤
      (2280822469190898733897 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2280822469190898733897 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2321213775258541 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2321213775258541 : ℝ) =
              (2321213775258541 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau163)
  have hz1 :
    (10000000000000000 / 2321213775258541 : ℝ) ≤
      1 / Real.sqrt (107760667809 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2321213775258541 : ℝ) =
          1 / (2321213775258541 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1160606887629269 : ℝ) ≤
      (3125186301868497031861 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (107760667809 / 2000000000000 : ℝ) ≤
      (375000000000000 / 1160606887629269 : ℝ) := by
    rw [show
        (375000000000000 / 1160606887629269 : ℝ) =
          (3 / 40) / (1160606887629269 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2280822469190898733897 / 10000000000000000000000 : ℝ)) -
        6 * (3125186301868497031861 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (107760667809 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (107760667809 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1160606887629269 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2280822469190898733897 / 10000000000000000000000 : ℝ)) -
          6 * (3125186301868497031861 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (107760667809 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (107760667809 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (107760667809 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_102 :
    ((134744360763168781831 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(27968538997595321615371 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2353224986307353 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (23111755917091873053 / 100000000000000000000 : ℝ)) -
              6 * (192833591403646283279 / 625000000000000000000 : ℝ)))) ≤
      Vfield (886026853789 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (886026853789 / 16000000000000 : ℝ)) =
      Real.log (16886026853789 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((886026853789 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (976026853789 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (134744360763168781831 / 2500000000000000000000 : ℝ) ≤
      Real.log (16886026853789 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (976026853789 / 16000000000000 : ℝ) ≤
      (-(27968538997595321615371 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (976026853789 / 16000000000000 : ℝ) = (976026853789 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (976026853789 / 500000000000 : ℝ) ≤
            (6688820017404678384629 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2353224986307353 / 10000000000000000 : ℝ) ≤ Real.sqrt (886026853789 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (886026853789 / 16000000000000 : ℝ) ≤ (588306246576839 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (886026853789 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau164 :
    Real.arctan (588306246576839 / 2500000000000000 : ℝ) ≤
      (23111755917091873053 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (23111755917091873053 / 100000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 588306246576839 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 588306246576839 : ℝ) =
              (588306246576839 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau164)
  have hz1 :
    (2500000000000000 / 588306246576839 : ℝ) ≤
      1 / Real.sqrt (886026853789 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 588306246576839 : ℝ) = 1 / (588306246576839 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2353224986307353 : ℝ) ≤
      (192833591403646283279 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (886026853789 / 16000000000000 : ℝ) ≤
      (750000000000000 / 2353224986307353 : ℝ) := by
    rw [show
        (750000000000000 / 2353224986307353 : ℝ) =
          (3 / 40) / (2353224986307353 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (23111755917091873053 / 100000000000000000000 : ℝ)) -
        6 * (192833591403646283279 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (886026853789 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (886026853789 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2353224986307353 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (23111755917091873053 / 100000000000000000000 : ℝ)) -
          6 * (192833591403646283279 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (886026853789 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (886026853789 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (886026853789 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_103 :
    ((138286424721773515033 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(13863101781672242510999 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1192403275103739 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2341078892322328510047 / 10000000000000000000000 : ℝ)) -
              6 * (3046976284942680492891 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (454984182553 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (454984182553 / 8000000000000 : ℝ)) =
      Real.log (8454984182553 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((454984182553 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (499984182553 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (138286424721773515033 / 2500000000000000000000 : ℝ) ≤
      Real.log (8454984182553 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (499984182553 / 8000000000000 : ℝ) ≤
      (-(13863101781672242510999 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (499984182553 / 8000000000000 : ℝ) = (499984182553 / 250000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (499984182553 / 250000000000 : ℝ) ≤
            (3465577725827757489001 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1192403275103739 / 5000000000000000 : ℝ) ≤ Real.sqrt (454984182553 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (454984182553 / 8000000000000 : ℝ) ≤ (2384806550207481 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (454984182553 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau165 :
    Real.arctan (2384806550207481 / 10000000000000000 : ℝ) ≤
      (2341078892322328510047 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2341078892322328510047 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2384806550207481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2384806550207481 : ℝ) =
              (2384806550207481 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau165)
  have hz1 :
    (10000000000000000 / 2384806550207481 : ℝ) ≤
      1 / Real.sqrt (454984182553 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2384806550207481 : ℝ) =
          1 / (2384806550207481 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 397467758367913 : ℝ) ≤
      (3046976284942680492891 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (454984182553 / 8000000000000 : ℝ) ≤
      (125000000000000 / 397467758367913 : ℝ) := by
    rw [show
        (125000000000000 / 397467758367913 : ℝ) =
          (3 / 40) / (1192403275103739 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2341078892322328510047 / 10000000000000000000000 : ℝ)) -
        6 * (3046976284942680492891 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (454984182553 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (454984182553 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1192403275103739 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2341078892322328510047 / 10000000000000000000000 : ℝ)) -
          6 * (3046976284942680492891 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (454984182553 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (454984182553 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (454984182553 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_104 :
    ((72677766318577952713 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(218067756075849292299 / 80000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2446747059541503 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1199801878895283653787 / 5000000000000000000000 : ℝ)) -
              6 * (594872574128161186261 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (47892569387 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47892569387 / 800000000000 : ℝ)) =
      Real.log (847892569387 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47892569387 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (52392569387 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (72677766318577952713 / 1250000000000000000000 : ℝ) ≤
      Real.log (847892569387 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (52392569387 / 800000000000 : ℝ) ≤
      (-(218067756075849292299 / 80000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (52392569387 / 800000000000 : ℝ) = (52392569387 / 50000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (52392569387 / 50000000000 : ℝ) ≤
            (3739341620150707701 / 80000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2446747059541503 / 10000000000000000 : ℝ) ≤ Real.sqrt (47892569387 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47892569387 / 800000000000 : ℝ) ≤ (1223373529770753 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47892569387 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau166 :
    Real.arctan (1223373529770753 / 5000000000000000 : ℝ) ≤
      (1199801878895283653787 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1199801878895283653787 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1223373529770753 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1223373529770753 : ℝ) =
              (1223373529770753 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau166)
  have hz1 :
    (5000000000000000 / 1223373529770753 : ℝ) ≤ 1 / Real.sqrt (47892569387 / 800000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1223373529770753 : ℝ) = 1 / (1223373529770753 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 815582353180501 : ℝ) ≤
      (594872574128161186261 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47892569387 / 800000000000 : ℝ) ≤
      (250000000000000 / 815582353180501 : ℝ) := by
    rw [show
        (250000000000000 / 815582353180501 : ℝ) =
          (3 / 40) / (2446747059541503 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1199801878895283653787 / 5000000000000000000000 : ℝ)) -
        6 * (594872574128161186261 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47892569387 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47892569387 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2446747059541503 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1199801878895283653787 / 5000000000000000000000 : ℝ)) -
          6 * (594872574128161186261 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (47892569387 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47892569387 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47892569387 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_105 :
    ((609618831947161312673 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(26811638883410333602363 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1253578883121989 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1228261108513296682027 / 5000000000000000000000 : ℝ)) -
              6 * (290670848125288106191 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (502867205187 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (502867205187 / 8000000000000 : ℝ)) =
      Real.log (8502867205187 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((502867205187 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (547867205187 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (609618831947161312673 / 10000000000000000000000 : ℝ) ≤
      Real.log (8502867205187 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (547867205187 / 8000000000000 : ℝ) ≤
      (-(26811638883410333602363 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (547867205187 / 8000000000000 : ℝ) = (547867205187 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (547867205187 / 500000000000 : ℝ) ≤
            (914248328589666397637 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1253578883121989 / 5000000000000000 : ℝ) ≤ Real.sqrt (502867205187 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (502867205187 / 8000000000000 : ℝ) ≤ (2507157766243981 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (502867205187 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau167 :
    Real.arctan (2507157766243981 / 10000000000000000 : ℝ) ≤
      (1228261108513296682027 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1228261108513296682027 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2507157766243981 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2507157766243981 : ℝ) =
              (2507157766243981 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau167)
  have hz1 :
    (10000000000000000 / 2507157766243981 : ℝ) ≤
      1 / Real.sqrt (502867205187 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2507157766243981 : ℝ) =
          1 / (2507157766243981 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1253578883121989 : ℝ) ≤
      (290670848125288106191 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (502867205187 / 8000000000000 : ℝ) ≤
      (375000000000000 / 1253578883121989 : ℝ) := by
    rw [show
        (375000000000000 / 1253578883121989 : ℝ) =
          (3 / 40) / (1253578883121989 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1228261108513296682027 / 5000000000000000000000 : ℝ)) -
        6 * (290670848125288106191 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (502867205187 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (502867205187 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1253578883121989 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1228261108513296682027 / 5000000000000000000000 : ℝ)) -
          6 * (290670848125288106191 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (502867205187 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (502867205187 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (502867205187 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_106 :
    ((63773625144515066253 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(26383922958767512167317 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2566146713712993 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2511944817458580581319 / 10000000000000000000000 : ℝ)) -
              6 * (2843472865197113350371 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (65851089563 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (65851089563 / 1000000000000 : ℝ)) =
      Real.log (1065851089563 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((65851089563 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (71476089563 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (63773625144515066253 / 1000000000000000000000 : ℝ) ≤
      Real.log (1065851089563 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (71476089563 / 1000000000000 : ℝ) ≤
      (-(26383922958767512167317 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (71476089563 / 1000000000000 : ℝ) = (71476089563 / 62500000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (71476089563 / 62500000000 : ℝ) ≤
            (1341964253232487832683 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2566146713712993 / 10000000000000000 : ℝ) ≤ Real.sqrt (65851089563 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (65851089563 / 1000000000000 : ℝ) ≤ (641536678428249 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (65851089563 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau168 :
    Real.arctan (641536678428249 / 2500000000000000 : ℝ) ≤
      (2511944817458580581319 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2511944817458580581319 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 641536678428249 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 641536678428249 : ℝ) =
              (641536678428249 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau168)
  have hz1 :
    (2500000000000000 / 641536678428249 : ℝ) ≤ 1 / Real.sqrt (65851089563 / 1000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 641536678428249 : ℝ) = 1 / (641536678428249 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 855382237904331 : ℝ) ≤
      (2843472865197113350371 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (65851089563 / 1000000000000 : ℝ) ≤
      (250000000000000 / 855382237904331 : ℝ) := by
    rw [show
        (250000000000000 / 855382237904331 : ℝ) =
          (3 / 40) / (2566146713712993 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2511944817458580581319 / 10000000000000000000000 : ℝ)) -
        6 * (2843472865197113350371 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (65851089563 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (65851089563 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2566146713712993 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2511944817458580581319 / 10000000000000000000000 : ℝ)) -
          6 * (2843472865197113350371 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (65851089563 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (65851089563 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (65851089563 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_107 :
    ((161897864139303837243 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(13118980103704165315979 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((646635646287919 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2531071162844353185537 / 10000000000000000000000 : ℝ)) -
              6 * (2822227043582772569641 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2140864814337 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2140864814337 / 32000000000000 : ℝ)) =
      Real.log (34140864814337 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2140864814337 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2320864814337 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (161897864139303837243 / 2500000000000000000000 : ℝ) ≤
      Real.log (34140864814337 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2320864814337 / 32000000000000 : ℝ) ≤
      (-(13118980103704165315979 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2320864814337 / 32000000000000 : ℝ) = (2320864814337 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2320864814337 / 2000000000000 : ℝ) ≤
            (743963502295834684021 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (646635646287919 / 2500000000000000 : ℝ) ≤ Real.sqrt (2140864814337 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2140864814337 / 32000000000000 : ℝ) ≤ (2586542585151679 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2140864814337 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau169 :
    Real.arctan (2586542585151679 / 10000000000000000 : ℝ) ≤
      (2531071162844353185537 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2531071162844353185537 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2586542585151679 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2586542585151679 : ℝ) =
              (2586542585151679 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau169)
  have hz1 :
    (10000000000000000 / 2586542585151679 : ℝ) ≤
      1 / Real.sqrt (2140864814337 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2586542585151679 : ℝ) =
          1 / (2586542585151679 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 646635646287919 : ℝ) ≤
      (2822227043582772569641 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2140864814337 / 32000000000000 : ℝ) ≤
      (187500000000000 / 646635646287919 : ℝ) := by
    rw [show
        (187500000000000 / 646635646287919 : ℝ) =
          (3 / 40) / (646635646287919 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2531071162844353185537 / 10000000000000000000000 : ℝ)) -
        6 * (2822227043582772569641 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2140864814337 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2140864814337 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((646635646287919 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2531071162844353185537 / 10000000000000000000000 : ℝ)) -
          6 * (2822227043582772569641 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2140864814337 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2140864814337 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2140864814337 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_108 :
    ((26297478348966672627 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(26094097354576342594779 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2606778880784913 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2550029181381709669393 / 10000000000000000000000 : ℝ)) -
              6 * (1400725358029980269551 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1087247381329 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1087247381329 / 16000000000000 : ℝ)) =
      Real.log (17087247381329 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1087247381329 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1177247381329 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (26297478348966672627 / 400000000000000000000 : ℝ) ≤
      Real.log (17087247381329 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1177247381329 / 16000000000000 : ℝ) ≤
      (-(26094097354576342594779 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1177247381329 / 16000000000000 : ℝ) = (1177247381329 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1177247381329 / 1000000000000 : ℝ) ≤
            (1631789857423657405221 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2606778880784913 / 10000000000000000 : ℝ) ≤ Real.sqrt (1087247381329 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1087247381329 / 16000000000000 : ℝ) ≤ (651694720196229 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1087247381329 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau170 :
    Real.arctan (651694720196229 / 2500000000000000 : ℝ) ≤
      (2550029181381709669393 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2550029181381709669393 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 651694720196229 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 651694720196229 : ℝ) =
              (651694720196229 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau170)
  have hz1 :
    (2500000000000000 / 651694720196229 : ℝ) ≤
      1 / Real.sqrt (1087247381329 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 651694720196229 : ℝ) = 1 / (651694720196229 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 868926293594971 : ℝ) ≤
      (1400725358029980269551 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1087247381329 / 16000000000000 : ℝ) ≤
      (250000000000000 / 868926293594971 : ℝ) := by
    rw [show
        (250000000000000 / 868926293594971 : ℝ) =
          (3 / 40) / (2606778880784913 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2550029181381709669393 / 10000000000000000000000 : ℝ)) -
        6 * (1400725358029980269551 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1087247381329 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1087247381329 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2606778880784913 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2550029181381709669393 / 10000000000000000000000 : ℝ)) -
          6 * (1400725358029980269551 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1087247381329 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1087247381329 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1087247381329 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
