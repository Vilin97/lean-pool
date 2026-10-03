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

/-! # V56: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_673 :
    ((6122387374240496023273 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1623057085064450056693 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1837994838888139 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1858030802236809204597 / 5000000000000000000000 : ℝ))) -
              6 * (407151059969191178087 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (54051600444471 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (54051600444471 / 64000000000000 : ℝ)) =
      Real.log (118051600444471 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((54051600444471 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (54411600444471 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (6122387374240496023273 / 10000000000000000000000 : ℝ) ≤
      Real.log (118051600444471 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (54411600444471 / 64000000000000 : ℝ) ≤
      (-(1623057085064450056693 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (54411600444471 / 64000000000000 : ℝ) = (54411600444471 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (54411600444471 / 32000000000000 : ℝ) ≤
            (5308414717935549943307 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1837994838888139 / 2000000000000000 : ℝ) ≤ Real.sqrt (54051600444471 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (54051600444471 / 64000000000000 : ℝ) ≤ (4594987097220349 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (54051600444471 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1118 :
    Real.arctan (4594987097220349 / 11790722084110163 : ℝ) ≤
      (1858030802236809204597 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1117 :
    Real.arctan (4594987097220349 / 5000000000000000 : ℝ) ≤
      (2 * (1858030802236809204597 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6790722084110163 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4594987097220349 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4594987097220349 / 5000000000000000 : ℝ) /
                (1 + (6790722084110163 / 5000000000000000 : ℝ)) =
              (4594987097220349 / 11790722084110163 : ℝ)
            by
        norm_num];
        exact hau1118)
  have hat1 :
    (Real.pi / 2 - (2 * (1858030802236809204597 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4594987097220349 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4594987097220349 : ℝ) =
              (4594987097220349 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1117)
  have hz1 :
    (5000000000000000 / 4594987097220349 : ℝ) ≤
      1 / Real.sqrt (54051600444471 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4594987097220349 : ℝ) = 1 / (4594987097220349 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1837994838888139 : ℝ) ≤
      (407151059969191178087 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (54051600444471 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1837994838888139 : ℝ) := by
    rw [show
        (150000000000000 / 1837994838888139 : ℝ) =
          (3 / 40) / (1837994838888139 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1858030802236809204597 / 5000000000000000000000 : ℝ))) -
        6 * (407151059969191178087 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (54051600444471 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (54051600444471 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1837994838888139 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1858030802236809204597 / 5000000000000000000000 : ℝ))) -
          6 * (407151059969191178087 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (54051600444471 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (54051600444471 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (54051600444471 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_674 :
    ((389249904457505137419 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1395321619366648151237 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((9295913345121237 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1872313611514181767439 / 5000000000000000000000 : ℝ))) -
              6 * (805062351806162380989 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (27652481574401 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (27652481574401 / 32000000000000 : ℝ)) =
      Real.log (59652481574401 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((27652481574401 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (27832481574401 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (389249904457505137419 / 625000000000000000000 : ℝ) ≤
      Real.log (59652481574401 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (27832481574401 / 32000000000000 : ℝ) ≤
      (-(1395321619366648151237 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27832481574401 / 32000000000000 : ℝ) = (27832481574401 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27832481574401 / 16000000000000 : ℝ) ≤
            (5536150183633351848763 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (9295913345121237 / 10000000000000000 : ℝ) ≤
      Real.sqrt (27652481574401 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (27652481574401 / 32000000000000 : ℝ) ≤ (232397833628031 / 250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (27652481574401 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1120 :
    Real.arctan (4647956672560620 / 11826675708571543 : ℝ) ≤
      (1872313611514181767439 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1119 :
    Real.arctan (232397833628031 / 250000000000000 : ℝ) ≤
      (2 * (1872313611514181767439 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6826675708571543 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (232397833628031 / 250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (232397833628031 / 250000000000000 : ℝ) /
                (1 + (6826675708571543 / 5000000000000000 : ℝ)) =
              (4647956672560620 / 11826675708571543 : ℝ)
            by
        norm_num];
        exact hau1120)
  have hat1 :
    (Real.pi / 2 - (2 * (1872313611514181767439 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (250000000000000 / 232397833628031 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 232397833628031 : ℝ) =
              (232397833628031 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hau1119)
  have hz1 :
    (250000000000000 / 232397833628031 : ℝ) ≤
      1 / Real.sqrt (27652481574401 / 32000000000000 : ℝ) := by
    rw [show (250000000000000 / 232397833628031 : ℝ) = 1 / (232397833628031 / 250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 3098637781707079 : ℝ) ≤
      (805062351806162380989 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (27652481574401 / 32000000000000 : ℝ) ≤
      (250000000000000 / 3098637781707079 : ℝ) := by
    rw [show
        (250000000000000 / 3098637781707079 : ℝ) =
          (3 / 40) / (9295913345121237 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1872313611514181767439 / 5000000000000000000000 : ℝ))) -
        6 * (805062351806162380989 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (27652481574401 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (27652481574401 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((9295913345121237 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1872313611514181767439 / 5000000000000000000000 : ℝ))) -
          6 * (805062351806162380989 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (27652481574401 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (27652481574401 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (27652481574401 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_675 :
    ((6332505844415552817503 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(586328612943406901771 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1880131741613021 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3772575766913640194333 / 10000000000000000000000 : ℝ))) -
              6 * (796130138632003110727 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (56558325853133 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (56558325853133 / 64000000000000 : ℝ)) =
      Real.log (120558325853133 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((56558325853133 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (56918325853133 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (6332505844415552817503 / 10000000000000000000000 : ℝ) ≤
      Real.log (120558325853133 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (56918325853133 / 64000000000000 : ℝ) ≤
      (-(586328612943406901771 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (56918325853133 / 64000000000000 : ℝ) = (56918325853133 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (56918325853133 / 32000000000000 : ℝ) ≤
            (2879407288556593098229 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1880131741613021 / 2000000000000000 : ℝ) ≤ Real.sqrt (56558325853133 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (56558325853133 / 64000000000000 : ℝ) ≤ (2350164677016277 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (56558325853133 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1122 :
    Real.arctan (9400658708065108 / 23724881935576725 : ℝ) ≤
      (3772575766913640194333 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1121 :
    Real.arctan (2350164677016277 / 2500000000000000 : ℝ) ≤
      (2 * (3772575766913640194333 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (548995277423069 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (2350164677016277 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2350164677016277 / 2500000000000000 : ℝ) /
                (1 + (548995277423069 / 400000000000000 : ℝ)) =
              (9400658708065108 / 23724881935576725 : ℝ)
            by
        norm_num];
        exact hau1122)
  have hat1 :
    (Real.pi / 2 - (2 * (3772575766913640194333 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2350164677016277 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2350164677016277 : ℝ) =
              (2350164677016277 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1121)
  have hz1 :
    (2500000000000000 / 2350164677016277 : ℝ) ≤
      1 / Real.sqrt (56558325853133 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2350164677016277 : ℝ) = 1 / (2350164677016277 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1880131741613021 : ℝ) ≤
      (796130138632003110727 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (56558325853133 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1880131741613021 : ℝ) := by
    rw [show
        (150000000000000 / 1880131741613021 : ℝ) =
          (3 / 40) / (1880131741613021 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3772575766913640194333 / 10000000000000000000000 : ℝ))) -
        6 * (796130138632003110727 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (56558325853133 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (56558325853133 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1880131741613021 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3772575766913640194333 / 10000000000000000000000 : ℝ))) -
          6 * (796130138632003110727 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (56558325853133 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (56558325853133 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (56558325853133 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_676 :
    ((1287186464959551226363 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(954842976206395349259 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((9504249753191331 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (379993042391329462331 / 1000000000000000000000 : ℝ))) -
              6 * (196872197076237575761 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (7226461069683 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7226461069683 / 8000000000000 : ℝ)) =
      Real.log (15226461069683 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7226461069683 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7271461069683 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1287186464959551226363 / 2000000000000000000000 : ℝ) ≤
      Real.log (15226461069683 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7271461069683 / 8000000000000 : ℝ) ≤
      (-(954842976206395349259 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (7271461069683 / 8000000000000 : ℝ) = (7271461069683 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7271461069683 / 4000000000000 : ℝ) ≤
            (5976628826793604650741 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (9504249753191331 / 10000000000000000 : ℝ) ≤ Real.sqrt (7226461069683 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7226461069683 / 8000000000000 : ℝ) ≤ (4752124876595667 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7226461069683 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1124 :
    Real.arctan (9504249753191334 / 23796041583404911 : ℝ) ≤
      (379993042391329462331 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1123 :
    Real.arctan (4752124876595667 / 5000000000000000 : ℝ) ≤
      (2 * (379993042391329462331 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13796041583404911 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4752124876595667 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4752124876595667 / 5000000000000000 : ℝ) /
                (1 + (13796041583404911 / 10000000000000000 : ℝ)) =
              (9504249753191334 / 23796041583404911 : ℝ)
            by
        norm_num];
        exact hau1124)
  have hat1 :
    (Real.pi / 2 - (2 * (379993042391329462331 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4752124876595667 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4752124876595667 : ℝ) =
              (4752124876595667 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1123)
  have hz1 :
    (5000000000000000 / 4752124876595667 : ℝ) ≤
      1 / Real.sqrt (7226461069683 / 8000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4752124876595667 : ℝ) = 1 / (4752124876595667 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 3168083251063777 : ℝ) ≤
      (196872197076237575761 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7226461069683 / 8000000000000 : ℝ) ≤
      (250000000000000 / 3168083251063777 : ℝ) := by
    rw [show
        (250000000000000 / 3168083251063777 : ℝ) =
          (3 / 40) / (9504249753191331 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (379993042391329462331 / 1000000000000000000000 : ℝ))) -
        6 * (196872197076237575761 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7226461069683 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7226461069683 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((9504249753191331 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (379993042391329462331 / 1000000000000000000000 : ℝ))) -
          6 * (196872197076237575761 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (7226461069683 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7226461069683 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7226461069683 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_677 :
    ((6639630455055536452119 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(532950666319523470387 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((9708116285978029 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (770588915703197956467 / 2000000000000000000000 : ℝ))) -
              6 * (385508999245285394263 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (30159206983063 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (30159206983063 / 32000000000000 : ℝ)) =
      Real.log (62159206983063 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((30159206983063 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (30339206983063 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (6639630455055536452119 / 10000000000000000000000 : ℝ) ≤
      Real.log (62159206983063 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (30339206983063 / 32000000000000 : ℝ) ≤
      (-(532950666319523470387 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (30339206983063 / 32000000000000 : ℝ) = (30339206983063 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30339206983063 / 16000000000000 : ℝ) ≤
            (6398521136680476529613 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (9708116285978029 / 10000000000000000 : ℝ) ≤
      Real.sqrt (30159206983063 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (30159206983063 / 32000000000000 : ℝ) ≤ (606757267873627 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (30159206983063 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1126 :
    Real.arctan (4854058142989016 / 11968635480172425 : ℝ) ≤
      (770588915703197956467 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1125 :
    Real.arctan (606757267873627 / 625000000000000 : ℝ) ≤
      (2 * (770588915703197956467 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (278745419206897 / 200000000000000 : ℝ) ≤
          Real.sqrt (1 + (606757267873627 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (606757267873627 / 625000000000000 : ℝ) /
                (1 + (278745419206897 / 200000000000000 : ℝ)) =
              (4854058142989016 / 11968635480172425 : ℝ)
            by
        norm_num];
        exact hau1126)
  have hat1 :
    (Real.pi / 2 - (2 * (770588915703197956467 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 606757267873627 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 606757267873627 : ℝ) =
              (606757267873627 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau1125)
  have hz1 :
    (625000000000000 / 606757267873627 : ℝ) ≤
      1 / Real.sqrt (30159206983063 / 32000000000000 : ℝ) := by
    rw [show (625000000000000 / 606757267873627 : ℝ) = 1 / (606757267873627 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 9708116285978029 : ℝ) ≤
      (385508999245285394263 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (30159206983063 / 32000000000000 : ℝ) ≤
      (750000000000000 / 9708116285978029 : ℝ) := by
    rw [show
        (750000000000000 / 9708116285978029 : ℝ) =
          (3 / 40) / (9708116285978029 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (770588915703197956467 / 2000000000000000000000 : ℝ))) -
        6 * (385508999245285394263 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (30159206983063 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (30159206983063 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((9708116285978029 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (770588915703197956467 / 2000000000000000000000 : ℝ))) -
          6 * (385508999245285394263 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (30159206983063 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (30159206983063 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (30159206983063 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_678 :
    ((3419630995230294538113 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(64069730353516965177 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4953894434510747 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3903831421400330573611 / 10000000000000000000000 : ℝ))) -
              6 * (377769635349620863439 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (15706284843697 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (15706284843697 / 16000000000000 : ℝ)) =
      Real.log (31706284843697 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((15706284843697 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (15796284843697 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3419630995230294538113 / 5000000000000000000000 : ℝ) ≤
      Real.log (31706284843697 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (15796284843697 / 16000000000000 : ℝ) ≤
      (-(64069730353516965177 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (15796284843697 / 16000000000000 : ℝ) = (15796284843697 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15796284843697 / 8000000000000 : ℝ) ≤
            (3401666171146483034823 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4953894434510747 / 5000000000000000 : ℝ) ≤ Real.sqrt (15706284843697 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (15706284843697 / 16000000000000 : ℝ) ≤
      (9907788869021497 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (15706284843697 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1128 :
    Real.arctan (9907788869021497 / 24077083514460878 : ℝ) ≤
      (3903831421400330573611 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1127 :
    Real.arctan (9907788869021497 / 10000000000000000 : ℝ) ≤
      (2 * (3903831421400330573611 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (7038541757230439 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (9907788869021497 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (9907788869021497 / 10000000000000000 : ℝ) /
                (1 + (7038541757230439 / 5000000000000000 : ℝ)) =
              (9907788869021497 / 24077083514460878 : ℝ)
            by
        norm_num];
        exact hau1128)
  have hat1 :
    (Real.pi / 2 - (2 * (3903831421400330573611 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 9907788869021497 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 9907788869021497 : ℝ) =
              (9907788869021497 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1127)
  have hz1 :
    (10000000000000000 / 9907788869021497 : ℝ) ≤
      1 / Real.sqrt (15706284843697 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 9907788869021497 : ℝ) =
          1 / (9907788869021497 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4953894434510747 : ℝ) ≤
      (377769635349620863439 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (15706284843697 / 16000000000000 : ℝ) ≤
      (375000000000000 / 4953894434510747 : ℝ) := by
    rw [show
        (375000000000000 / 4953894434510747 : ℝ) =
          (3 / 40) / (4953894434510747 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3903831421400330573611 / 10000000000000000000000 : ℝ))) -
        6 * (377769635349620863439 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (15706284843697 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (15706284843697 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4953894434510747 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3903831421400330573611 / 10000000000000000000000 : ℝ))) -
          6 * (377769635349620863439 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (15706284843697 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (15706284843697 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (15706284843697 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_679 :
    ((3613476445799885952621 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (158852024015426556119 / 2500000000000000000000 : ℝ) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5147761580900357 / 5000000000000000 : ℝ) *
            (Real.pi + (2 * (481773868711436053381 / 1250000000000000000000 : ℝ)) -
              6 * (727187456097735281609 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4239911887007 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4239911887007 / 4000000000000 : ℝ)) =
      Real.log (8239911887007 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4239911887007 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4262411887007 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3613476445799885952621 / 5000000000000000000000 : ℝ) ≤
      Real.log (8239911887007 / 4000000000000 : ℝ) := by
    have h :=
      log_ge_of_split_pos 1
        (show (8239911887007 / 4000000000000 : ℝ) = 2 ^ 1 * (8239911887007 / 8000000000000 : ℝ) by
          norm_num)
        (by norm_num)
        (log_ge_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          (147740544299885952621 / 5000000000000000000000 : ℝ) ≤
            Real.log (8239911887007 / 8000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hU2 :
    Real.log (4262411887007 / 4000000000000 : ℝ) ≤
      (158852024015426556119 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hs_lo :
    (5147761580900357 / 5000000000000000 : ℝ) ≤ Real.sqrt (4239911887007 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4239911887007 / 4000000000000 : ℝ) ≤ (10295523161800717 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4239911887007 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hal1129 :
    (481773868711436053381 / 1250000000000000000000 : ℝ) ≤
      Real.arctan (10000000000000000000000000000000 / 24648146516963879478122821351257 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (2 * (481773868711436053381 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 10295523161800717 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (10000000000000000 / 10295523161800717 : ℝ) ^ 2) ≤
          (1394064500618621 / 1000000000000000 : ℝ))
      (by
        rw [show
            (10000000000000000 / 10295523161800717 : ℝ) /
                (1 + (1394064500618621 / 1000000000000000 : ℝ)) =
              (10000000000000000000000000000000 / 24648146516963879478122821351257 : ℝ)
            by
        norm_num];
        exact hal1129)
  have hz1 :
    (10000000000000000 / 10295523161800717 : ℝ) ≤
      1 / Real.sqrt (4239911887007 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 10295523161800717 : ℝ) =
          1 / (10295523161800717 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 5147761580900357 : ℝ) ≤
      (727187456097735281609 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4239911887007 / 4000000000000 : ℝ) ≤
      (375000000000000 / 5147761580900357 : ℝ) := by
    rw [show
        (375000000000000 / 5147761580900357 : ℝ) =
          (3 / 40) / (5147761580900357 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (2 * (481773868711436053381 / 1250000000000000000000 : ℝ)) -
        6 * (727187456097735281609 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4239911887007 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4239911887007 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5147761580900357 / 5000000000000000 : ℝ) *
        (Real.pi + (2 * (481773868711436053381 / 1250000000000000000000 : ℝ)) -
          6 * (727187456097735281609 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4239911887007 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4239911887007 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4239911887007 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_680 :
    ((1520034531928750963607 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (1344768187442564119861 / 10000000000000000000000 : ℝ) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5334587942785359 / 5000000000000000 : ℝ) *
            (Real.pi + (2 * (3765169602758050855633 / 10000000000000000000000 : ℝ)) -
              6 * (21931411260193838793 / 312500000000000000000 : ℝ)))) ≤
      Vfield (18213010252359 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18213010252359 / 16000000000000 : ℝ)) =
      Real.log (34213010252359 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18213010252359 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18303010252359 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1520034531928750963607 / 2000000000000000000000 : ℝ) ≤
      Real.log (34213010252359 / 16000000000000 : ℝ) := by
    have h :=
      log_ge_of_split_pos 1
        (show
          (34213010252359 / 16000000000000 : ℝ) = 2 ^ 1 * (34213010252359 / 32000000000000 : ℝ) by
          norm_num)
        (by norm_num)
        (log_ge_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          (133740171328750963607 / 2000000000000000000000 : ℝ) ≤
            Real.log (34213010252359 / 32000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hU2 :
    Real.log (18303010252359 / 16000000000000 : ℝ) ≤
      (1344768187442564119861 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hs_lo :
    (5334587942785359 / 5000000000000000 : ℝ) ≤ Real.sqrt (18213010252359 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18213010252359 / 16000000000000 : ℝ) ≤
      (10669175885570721 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18213010252359 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hal1130 :
    (3765169602758050855633 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (100000000000000000000000000000000 / 252921480211266056994548940029691 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (2 * (3765169602758050855633 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 10669175885570721 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (10000000000000000 / 10669175885570721 : ℝ) ^ 2) ≤
          (13705812231788571 / 10000000000000000 : ℝ))
      (by
        rw [show
            (10000000000000000 / 10669175885570721 : ℝ) /
                (1 + (13705812231788571 / 10000000000000000 : ℝ)) =
              (100000000000000000000000000000000 / 252921480211266056994548940029691 : ℝ)
            by
        norm_num];
        exact hal1130)
  have hz1 :
    (10000000000000000 / 10669175885570721 : ℝ) ≤
      1 / Real.sqrt (18213010252359 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 10669175885570721 : ℝ) =
          1 / (10669175885570721 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1778195980928453 : ℝ) ≤
      (21931411260193838793 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18213010252359 / 16000000000000 : ℝ) ≤
      (125000000000000 / 1778195980928453 : ℝ) := by
    rw [show
        (125000000000000 / 1778195980928453 : ℝ) =
          (3 / 40) / (5334587942785359 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (2 * (3765169602758050855633 / 10000000000000000000000 : ℝ)) -
        6 * (21931411260193838793 / 312500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18213010252359 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18213010252359 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5334587942785359 / 5000000000000000 : ℝ) *
        (Real.pi + (2 * (3765169602758050855633 / 10000000000000000000000 : ℝ)) -
          6 * (21931411260193838793 / 312500000000000000000 : ℝ))) ≤
      Real.sqrt (18213010252359 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18213010252359 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18213010252359 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_681 :
    ((3979981422045415289587 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (1003562467551241527391 / 5000000000000000000000 : ℝ) -
            2 +
          12 * (3 / 40) +
        2 *
          ((11030178193452383 / 10000000000000000 : ℝ) *
            (Real.pi + (2 * (1841128949775744109199 / 5000000000000000000000 : ℝ)) -
              6 * (339453879744246898597 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1946637295669 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1946637295669 / 1600000000000 : ℝ)) =
      Real.log (3546637295669 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1946637295669 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1955637295669 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3979981422045415289587 / 5000000000000000000000 : ℝ) ≤
      Real.log (3546637295669 / 1600000000000 : ℝ) := by
    have h :=
      log_ge_of_split_pos 1
        (show (3546637295669 / 1600000000000 : ℝ) = 2 ^ 1 * (3546637295669 / 3200000000000 : ℝ) by
          norm_num)
        (by norm_num)
        (log_ge_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          (514245520545415289587 / 5000000000000000000000 : ℝ) ≤
            Real.log (3546637295669 / 3200000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hU2 :
    Real.log (1955637295669 / 1600000000000 : ℝ) ≤
      (1003562467551241527391 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hs_lo :
    (11030178193452383 / 10000000000000000 : ℝ) ≤ Real.sqrt (1946637295669 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1946637295669 / 1600000000000 : ℝ) ≤ (5515089096726193 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1946637295669 / 1600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hal1131 :
    (1841128949775744109199 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (50000000000000000000000000000000 / 129592954174045864388334571323681 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (2 * (1841128949775744109199 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 5515089096726193 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (5000000000000000 / 5515089096726193 : ℝ) ^ 2) ≤
          (13497889499368817 / 10000000000000000 : ℝ))
      (by
        rw [show
            (5000000000000000 / 5515089096726193 : ℝ) /
                (1 + (13497889499368817 / 10000000000000000 : ℝ)) =
              (50000000000000000000000000000000 / 129592954174045864388334571323681 : ℝ)
            by
        norm_num];
        exact hal1131)
  have hz1 :
    (5000000000000000 / 5515089096726193 : ℝ) ≤
      1 / Real.sqrt (1946637295669 / 1600000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 5515089096726193 : ℝ) = 1 / (5515089096726193 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 11030178193452383 : ℝ) ≤
      (339453879744246898597 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1946637295669 / 1600000000000 : ℝ) ≤
      (750000000000000 / 11030178193452383 : ℝ) := by
    rw [show
        (750000000000000 / 11030178193452383 : ℝ) =
          (3 / 40) / (11030178193452383 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (2 * (1841128949775744109199 / 5000000000000000000000 : ℝ)) -
        6 * (339453879744246898597 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1946637295669 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1946637295669 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((11030178193452383 / 10000000000000000 : ℝ) *
        (Real.pi + (2 * (1841128949775744109199 / 5000000000000000000000 : ℝ)) -
          6 * (339453879744246898597 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1946637295669 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1946637295669 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1946637295669 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_682 :
    ((216072312191625710833 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (3213177334616844766239 / 10000000000000000000000 : ℝ) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5859433948417073 / 5000000000000000 : ℝ) *
            (Real.pi + (2 * (1766052720082905933429 / 5000000000000000000000 : ℝ)) -
              6 * (639121915477979050969 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2746637295669 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2746637295669 / 2000000000000 : ℝ)) =
      Real.log (4746637295669 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2746637295669 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2757887295669 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (216072312191625710833 / 250000000000000000000 : ℝ) ≤
      Real.log (4746637295669 / 2000000000000 : ℝ) := by
    have h :=
      log_ge_of_split_pos 1
        (show (4746637295669 / 2000000000000 : ℝ) = 2 ^ 1 * (4746637295669 / 4000000000000 : ℝ) by
          norm_num)
        (by norm_num)
        (log_ge_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          (42785517116625710833 / 250000000000000000000 : ℝ) ≤
            Real.log (4746637295669 / 4000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hU2 :
    Real.log (2757887295669 / 2000000000000 : ℝ) ≤
      (3213177334616844766239 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hs_lo :
    (5859433948417073 / 5000000000000000 : ℝ) ≤ Real.sqrt (2746637295669 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2746637295669 / 2000000000000 : ℝ) ≤ (11718867896834149 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2746637295669 / 2000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hal1132 :
    (1766052720082905933429 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (12500000000000000000000000000000 / 33905558639632100095102679201933 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (2 * (1766052720082905933429 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 11718867896834149 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (10000000000000000 / 11718867896834149 : ℝ) ^ 2) ≤
          (1643245229668617 / 1250000000000000 : ℝ))
      (by
        rw [show
            (10000000000000000 / 11718867896834149 : ℝ) /
                (1 + (1643245229668617 / 1250000000000000 : ℝ)) =
              (12500000000000000000000000000000 / 33905558639632100095102679201933 : ℝ)
            by
        norm_num];
        exact hal1132)
  have hz1 :
    (10000000000000000 / 11718867896834149 : ℝ) ≤
      1 / Real.sqrt (2746637295669 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 11718867896834149 : ℝ) =
          1 / (11718867896834149 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 5859433948417073 : ℝ) ≤
      (639121915477979050969 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2746637295669 / 2000000000000 : ℝ) ≤
      (375000000000000 / 5859433948417073 : ℝ) := by
    rw [show
        (375000000000000 / 5859433948417073 : ℝ) =
          (3 / 40) / (5859433948417073 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (2 * (1766052720082905933429 / 5000000000000000000000 : ℝ)) -
        6 * (639121915477979050969 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2746637295669 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2746637295669 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5859433948417073 / 5000000000000000 : ℝ) *
        (Real.pi + (2 * (1766052720082905933429 / 5000000000000000000000 : ℝ)) -
          6 * (639121915477979050969 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2746637295669 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2746637295669 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2746637295669 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_683 :
    ((247074633638366187549 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (1052158574414174657667 / 2000000000000000000000 : ℝ) -
            2 +
          12 * (3 / 40) +
        2 *
          ((12987144889918067 / 10000000000000000 : ℝ) *
            (Real.pi + (2 * (102527157563947062571 / 312500000000000000000 : ℝ)) -
              6 * (288426718122331681813 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (6746637295669 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6746637295669 / 4000000000000 : ℝ)) =
      Real.log (10746637295669 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6746637295669 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6769137295669 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (247074633638366187549 / 250000000000000000000 : ℝ) ≤
      Real.log (10746637295669 / 4000000000000 : ℝ) := by
    have h :=
      log_ge_of_split_pos 1
        (show (10746637295669 / 4000000000000 : ℝ) = 2 ^ 1 * (10746637295669 / 8000000000000 : ℝ)
          by norm_num)
        (by norm_num)
        (log_ge_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          (73787838563366187549 / 250000000000000000000 : ℝ) ≤
            Real.log (10746637295669 / 8000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hU2 :
    Real.log (6769137295669 / 4000000000000 : ℝ) ≤
      (1052158574414174657667 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hs_lo :
    (12987144889918067 / 10000000000000000 : ℝ) ≤ Real.sqrt (6746637295669 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6746637295669 / 4000000000000 : ℝ) ≤ (1298714488991807 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6746637295669 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hal1133 :
    (102527157563947062571 / 312500000000000000000 : ℝ) ≤
      Real.arctan (5000000000000000000000000000000 / 14689088481056534722184183966923 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (2 * (102527157563947062571 / 312500000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 1298714488991807 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (1000000000000000 / 1298714488991807 : ℝ) ^ 2) ≤
          (6310483255222389 / 5000000000000000 : ℝ))
      (by
        rw [show
            (1000000000000000 / 1298714488991807 : ℝ) /
                (1 + (6310483255222389 / 5000000000000000 : ℝ)) =
              (5000000000000000000000000000000 / 14689088481056534722184183966923 : ℝ)
            by
        norm_num];
        exact hal1133)
  have hz1 :
    (1000000000000000 / 1298714488991807 : ℝ) ≤
      1 / Real.sqrt (6746637295669 / 4000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 1298714488991807 : ℝ) = 1 / (1298714488991807 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 12987144889918067 : ℝ) ≤
      (288426718122331681813 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6746637295669 / 4000000000000 : ℝ) ≤
      (750000000000000 / 12987144889918067 : ℝ) := by
    rw [show
        (750000000000000 / 12987144889918067 : ℝ) =
          (3 / 40) / (12987144889918067 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (2 * (102527157563947062571 / 312500000000000000000 : ℝ)) -
        6 * (288426718122331681813 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6746637295669 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6746637295669 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((12987144889918067 / 10000000000000000 : ℝ) *
        (Real.pi + (2 * (102527157563947062571 / 312500000000000000000 : ℝ)) -
          6 * (288426718122331681813 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (6746637295669 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6746637295669 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6746637295669 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
