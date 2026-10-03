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

/-! # V01: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_13 :
    ((2838708958444624399 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51312936940985871685561 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((84248322090117 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ))))) ≤
      Vfield (283911191 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (283911191 / 1000000000000 : ℝ)) =
      Real.log (1000283911191 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((283911191 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5908911191 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2838708958444624399 / 10000000000000000000000 : ℝ) ≤
      Real.log (1000283911191 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5908911191 / 1000000000000 : ℝ) ≤
      (-(51312936940985871685561 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (5908911191 / 1000000000000 : ℝ) = (5908911191 / 3906250000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5908911191 / 3906250000 : ℝ) ≤
            (4138837483014128314439 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (168496644180231 / 10000000000000000 : ℝ) ≤ Real.sqrt (283911191 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (283911191 / 1000000000000 : ℝ) ≤ (84248322090117 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (283911191 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau27 :
    Real.arctan (84248322090117 / 5000000000000000 : ℝ) ≤
      (168480700868393777449 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 84248322090117 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 84248322090117 : ℝ) =
              (84248322090117 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau27)
  have hz1 :
    (5000000000000000 / 84248322090117 : ℝ) ≤ 1 / Real.sqrt (283911191 / 1000000000000 : ℝ) := by
    rw [show (5000000000000000 / 84248322090117 : ℝ) = 1 / (84248322090117 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal28 :
    (138120555504676214793 / 625000000000000000000 : ℝ) ≤
      Real.arctan (56165548060077 / 250000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 56165548060077 : ℝ) ≤
      (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 56165548060077 : ℝ) =
              (56165548060077 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal28)
  have hz2 :
    (3 / 40) / Real.sqrt (283911191 / 1000000000000 : ℝ) ≤
      (250000000000000 / 56165548060077 : ℝ) := by
    rw [show
        (250000000000000 / 56165548060077 : ℝ) =
          (3 / 40) / (168496644180231 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (283911191 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (283911191 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((84248322090117 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ)))) ≤
      Real.sqrt (283911191 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (283911191 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (283911191 / 1000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (283911191 / 1000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_14 :
    ((3400600750179924673 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51218264559151743459197 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((36884571408653 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ))))) ≤
      Vfield (170058951 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (170058951 / 500000000000 : ℝ)) = Real.log (500170058951 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((170058951 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2982558951 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3400600750179924673 / 10000000000000000000000 : ℝ) ≤
      Real.log (500170058951 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2982558951 / 500000000000 : ℝ) ≤
      (-(51218264559151743459197 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (2982558951 / 500000000000 : ℝ) = (2982558951 / 1953125000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2982558951 / 1953125000 : ℝ) ≤
            (4233509864848256540803 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (92211428521631 / 5000000000000000 : ℝ) ≤ Real.sqrt (170058951 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (170058951 / 500000000000 : ℝ) ≤ (36884571408653 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (170058951 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau29 :
    Real.arctan (36884571408653 / 2000000000000000 : ℝ) ≤
      (46100488200992503859 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 36884571408653 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 36884571408653 : ℝ) =
              (36884571408653 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau29)
  have hz1 :
    (2000000000000000 / 36884571408653 : ℝ) ≤ 1 / Real.sqrt (170058951 / 500000000000 : ℝ) := by
    rw [show (2000000000000000 / 36884571408653 : ℝ) = 1 / (36884571408653 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal30 :
    (37673974722398950663 / 156250000000000000000 : ℝ) ≤
      Real.arctan (92211428521631 / 375000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (375000000000000 / 92211428521631 : ℝ) ≤
      (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 92211428521631 : ℝ) =
              (92211428521631 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal30)
  have hz2 :
    (3 / 40) / Real.sqrt (170058951 / 500000000000 : ℝ) ≤
      (375000000000000 / 92211428521631 : ℝ) := by
    rw [show
        (375000000000000 / 92211428521631 : ℝ) =
          (3 / 40) / (92211428521631 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (170058951 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (170058951 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((36884571408653 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ)))) ≤
      Real.sqrt (170058951 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (170058951 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (170058951 / 500000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (170058951 / 500000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_15 :
    ((396246097145057287 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25562240032020096608843 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((24884879099817 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ))))) ≤
      Vfield (396324613 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (396324613 / 1000000000000 : ℝ)) =
      Real.log (1000396324613 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((396324613 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6021324613 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (396246097145057287 / 1000000000000000000000 : ℝ) ≤
      Real.log (1000396324613 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6021324613 / 1000000000000 : ℝ) ≤
      (-(25562240032020096608843 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (6021324613 / 1000000000000 : ℝ) = (6021324613 / 3906250000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6021324613 / 3906250000 : ℝ) ≤
            (2163647179979903391157 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (199079032798533 / 10000000000000000 : ℝ) ≤ Real.sqrt (396324613 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (396324613 / 1000000000000 : ℝ) ≤ (24884879099817 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (396324613 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau31 :
    Real.arctan (24884879099817 / 1250000000000000 : ℝ) ≤
      (99526369538609389173 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 24884879099817 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 24884879099817 : ℝ) =
              (24884879099817 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau31)
  have hz1 :
    (1250000000000000 / 24884879099817 : ℝ) ≤ 1 / Real.sqrt (396324613 / 1000000000000 : ℝ) := by
    rw [show (1250000000000000 / 24884879099817 : ℝ) = 1 / (24884879099817 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal32 :
    (324319511825085218099 / 1250000000000000000000 : ℝ) ≤
      Real.arctan (66359677599511 / 250000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 66359677599511 : ℝ) ≤
      (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 66359677599511 : ℝ) =
              (66359677599511 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal32)
  have hz2 :
    (3 / 40) / Real.sqrt (396324613 / 1000000000000 : ℝ) ≤
      (250000000000000 / 66359677599511 : ℝ) := by
    rw [show
        (250000000000000 / 66359677599511 : ℝ) =
          (3 / 40) / (199079032798533 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (396324613 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (396324613 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((24884879099817 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ)))) ≤
      Real.sqrt (396324613 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (396324613 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (396324613 / 1000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (396324613 / 1000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_16 :
    ((2435712931404190679 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25487292403074346048679 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((110369975480201 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ))))) ≤
      Vfield (974522519 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (974522519 / 2000000000000 : ℝ)) =
      Real.log (2000974522519 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((974522519 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (12224522519 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2435712931404190679 / 5000000000000000000000 : ℝ) ≤
      Real.log (2000974522519 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (12224522519 / 2000000000000 : ℝ) ≤
      (-(25487292403074346048679 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (12224522519 / 2000000000000 : ℝ) = (12224522519 / 7812500000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12224522519 / 7812500000 : ℝ) ≤
            (2238594808925653951321 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (220739950960399 / 10000000000000000 : ℝ) ≤ Real.sqrt (974522519 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (974522519 / 2000000000000 : ℝ) ≤ (110369975480201 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (974522519 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau33 :
    Real.arctan (110369975480201 / 5000000000000000 : ℝ) ≤
      (27588013595377272983 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 110369975480201 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 110369975480201 : ℝ) =
              (110369975480201 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau33)
  have hz1 :
    (5000000000000000 / 110369975480201 : ℝ) ≤ 1 / Real.sqrt (974522519 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 110369975480201 : ℝ) = 1 / (110369975480201 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal34 :
    (143118806689254327513 / 500000000000000000000 : ℝ) ≤
      Real.arctan (220739950960399 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 220739950960399 : ℝ) ≤
      (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 220739950960399 : ℝ) =
              (220739950960399 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal34)
  have hz2 :
    (3 / 40) / Real.sqrt (974522519 / 2000000000000 : ℝ) ≤
      (750000000000000 / 220739950960399 : ℝ) := by
    rw [show
        (750000000000000 / 220739950960399 : ℝ) =
          (3 / 40) / (220739950960399 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (974522519 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (974522519 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((110369975480201 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ)))) ≤
      Real.sqrt (974522519 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (974522519 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (974522519 / 2000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (974522519 / 2000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_17 :
    ((2890154069979049949 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25413451632679054566369 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((30057182637849 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (289098953 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (289098953 / 500000000000 : ℝ)) = Real.log (500289098953 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((289098953 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3101598953 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2890154069979049949 / 5000000000000000000000 : ℝ) ≤
      Real.log (500289098953 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3101598953 / 500000000000 : ℝ) ≤
      (-(25413451632679054566369 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (3101598953 / 500000000000 : ℝ) = (3101598953 / 1953125000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3101598953 / 1953125000 : ℝ) ≤
            (2312435579320945433631 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (240457461102789 / 10000000000000000 : ℝ) ≤ Real.sqrt (289098953 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (289098953 / 500000000000 : ℝ) ≤ (30057182637849 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (289098953 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau35 :
    Real.arctan (30057182637849 / 1250000000000000 : ℝ) ≤
      (120205566586796683229 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 30057182637849 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 30057182637849 : ℝ) =
              (30057182637849 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau35)
  have hz1 :
    (1250000000000000 / 30057182637849 : ℝ) ≤ 1 / Real.sqrt (289098953 / 500000000000 : ℝ) := by
    rw [show (1250000000000000 / 30057182637849 : ℝ) = 1 / (30057182637849 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal36 :
    (3102561376671980779519 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (80152487034263 / 250000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 80152487034263 : ℝ) ≤
      (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 80152487034263 : ℝ) =
              (80152487034263 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal36)
  have hz2 :
    (3 / 40) / Real.sqrt (289098953 / 500000000000 : ℝ) ≤
      (250000000000000 / 80152487034263 : ℝ) := by
    rw [show
        (250000000000000 / 80152487034263 : ℝ) =
          (3 / 40) / (240457461102789 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (289098953 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (289098953 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((30057182637849 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (289098953 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (289098953 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (289098953 / 500000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (289098953 / 500000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_18 :
    ((7296953385895796397 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(50585194098875661653047 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((270178021126813 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ))))) ≤
      Vfield (729961631 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (729961631 / 1000000000000 : ℝ)) =
      Real.log (1000729961631 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((729961631 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6354961631 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (7296953385895796397 / 10000000000000000000000 : ℝ) ≤
      Real.log (1000729961631 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6354961631 / 1000000000000 : ℝ) ≤
      (-(50585194098875661653047 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (6354961631 / 1000000000000 : ℝ) = (6354961631 / 3906250000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6354961631 / 3906250000 : ℝ) ≤
            (4866580325124338346953 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (27017802112681 / 1000000000000000 : ℝ) ≤ Real.sqrt (729961631 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (729961631 / 1000000000000 : ℝ) ≤ (270178021126813 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (729961631 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau37 :
    Real.arctan (270178021126813 / 10000000000000000 : ℝ) ≤
      (54022462008273651983 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 270178021126813 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 270178021126813 : ℝ) =
              (270178021126813 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau37)
  have hz1 :
    (10000000000000000 / 270178021126813 : ℝ) ≤ 1 / Real.sqrt (729961631 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 270178021126813 : ℝ) = 1 / (270178021126813 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal38 :
    (691531386986268494069 / 2000000000000000000000 : ℝ) ≤
      Real.arctan (27017802112681 / 75000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (75000000000000 / 27017802112681 : ℝ) ≤
      (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (75000000000000 / 27017802112681 : ℝ) =
              (27017802112681 / 75000000000000 : ℝ)
            by
        norm_num];
        exact hal38)
  have hz2 :
    (3 / 40) / Real.sqrt (729961631 / 1000000000000 : ℝ) ≤
      (75000000000000 / 27017802112681 : ℝ) := by
    rw [show
        (75000000000000 / 27017802112681 : ℝ) = (3 / 40) / (27017802112681 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (729961631 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (729961631 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((270178021126813 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ)))) ≤
      Real.sqrt (729961631 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (729961631 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (729961631 / 1000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (729961631 / 1000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_19 :
    ((1611037951921033759 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(50466495663078367309339 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((283873826461689 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (1611686987 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1611686987 / 2000000000000 : ℝ)) =
      Real.log (2001611686987 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1611686987 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (12861686987 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1611037951921033759 / 2000000000000000000000 : ℝ) ≤
      Real.log (2001611686987 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (12861686987 / 2000000000000 : ℝ) ≤
      (-(50466495663078367309339 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (12861686987 / 2000000000000 : ℝ) = (12861686987 / 7812500000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12861686987 / 7812500000 : ℝ) ≤
            (4985278760921632690661 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (141936913230843 / 5000000000000000 : ℝ) ≤ Real.sqrt (1611686987 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1611686987 / 2000000000000 : ℝ) ≤ (283873826461689 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1611686987 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau39 :
    Real.arctan (283873826461689 / 10000000000000000 : ℝ) ≤
      (283797610683746791347 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 283873826461689 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 283873826461689 : ℝ) =
              (283873826461689 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau39)
  have hz1 :
    (10000000000000000 / 283873826461689 : ℝ) ≤ 1 / Real.sqrt (1611686987 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 283873826461689 : ℝ) = 1 / (283873826461689 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal40 :
    (3618342583696765969299 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (47312304410281 / 125000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (125000000000000 / 47312304410281 : ℝ) ≤
      (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 47312304410281 : ℝ) =
              (47312304410281 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hal40)
  have hz2 :
    (3 / 40) / Real.sqrt (1611686987 / 2000000000000 : ℝ) ≤
      (125000000000000 / 47312304410281 : ℝ) := by
    rw [show
        (125000000000000 / 47312304410281 : ℝ) =
          (3 / 40) / (141936913230843 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1611686987 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1611686987 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((283873826461689 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (1611686987 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1611686987 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1611686987 / 2000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (1611686987 / 2000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_20 :
    ((35253474581734419 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6293648705936709382501 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((148469302887837 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (220431339 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (220431339 / 250000000000 : ℝ)) = Real.log (250220431339 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((220431339 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1626681339 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (35253474581734419 / 40000000000000000000 : ℝ) ≤ Real.log (250220431339 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1626681339 / 250000000000 : ℝ) ≤
      (-(6293648705936709382501 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1626681339 / 250000000000 : ℝ) = (1626681339 / 976562500 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1626681339 / 976562500 : ℝ) ≤
            (637823097063290617499 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (296938605775671 / 10000000000000000 : ℝ) ≤ Real.sqrt (220431339 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (220431339 / 250000000000 : ℝ) ≤ (148469302887837 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (220431339 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau41 :
    Real.arctan (148469302887837 / 5000000000000000 : ℝ) ≤
      (74212844787754867117 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 148469302887837 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 148469302887837 : ℝ) =
              (148469302887837 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau41)
  have hz1 :
    (5000000000000000 / 148469302887837 : ℝ) ≤ 1 / Real.sqrt (220431339 / 250000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 148469302887837 : ℝ) = 1 / (148469302887837 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal42 :
    (3769825878752123006391 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (98979535258557 / 250000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 98979535258557 : ℝ) ≤
      (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 98979535258557 : ℝ) =
              (98979535258557 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal42)
  have hz2 :
    (3 / 40) / Real.sqrt (220431339 / 250000000000 : ℝ) ≤
      (250000000000000 / 98979535258557 : ℝ) := by
    rw [show
        (250000000000000 / 98979535258557 : ℝ) =
          (3 / 40) / (296938605775671 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (220431339 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (220431339 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((148469302887837 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (220431339 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (220431339 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (220431339 / 250000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (220431339 / 250000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_21 :
    ((2528385230620046493 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(50151154605132541364319 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3180983626569 / 100000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (4047462733 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4047462733 / 4000000000000 : ℝ)) =
      Real.log (4004047462733 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4047462733 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (26547462733 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2528385230620046493 / 2500000000000000000000 : ℝ) ≤
      Real.log (4004047462733 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (26547462733 / 4000000000000 : ℝ) ≤
      (-(50151154605132541364319 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (26547462733 / 4000000000000 : ℝ) = (26547462733 / 15625000000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26547462733 / 15625000000 : ℝ) ≤
            (5300619818867458635681 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (318098362656897 / 10000000000000000 : ℝ) ≤ Real.sqrt (4047462733 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4047462733 / 4000000000000 : ℝ) ≤ (3180983626569 / 100000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4047462733 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau43 :
    Real.arctan (3180983626569 / 100000000000000 : ℝ) ≤
      (79497784202311396663 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (100000000000000 / 3180983626569 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (100000000000000 / 3180983626569 : ℝ) =
              (3180983626569 / 100000000000000 : ℝ)
            by
        norm_num];
        exact hau43)
  have hz1 :
    (100000000000000 / 3180983626569 : ℝ) ≤ 1 / Real.sqrt (4047462733 / 4000000000000 : ℝ) := by
    rw [show (100000000000000 / 3180983626569 : ℝ) = 1 / (3180983626569 / 100000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal44 :
    (2005672468682107829937 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (106032787552299 / 250000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 106032787552299 : ℝ) ≤
      (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 106032787552299 : ℝ) =
              (106032787552299 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal44)
  have hz2 :
    (3 / 40) / Real.sqrt (4047462733 / 4000000000000 : ℝ) ≤
      (250000000000000 / 106032787552299 : ℝ) := by
    rw [show
        (250000000000000 / 106032787552299 : ℝ) =
          (3 / 40) / (318098362656897 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4047462733 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4047462733 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3180983626569 / 100000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (4047462733 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4047462733 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4047462733 / 4000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (4047462733 / 4000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_22 :
    ((5706772088353681693 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24978482657227015538013 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((67587158854327 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (2284012021 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2284012021 / 2000000000000 : ℝ)) =
      Real.log (2002284012021 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2284012021 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (13534012021 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5706772088353681693 / 5000000000000000000000 : ℝ) ≤
      Real.log (2002284012021 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (13534012021 / 2000000000000 : ℝ) ≤
      (-(24978482657227015538013 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (13534012021 / 2000000000000 : ℝ) = (13534012021 / 7812500000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13534012021 / 7812500000 : ℝ) ≤
            (2747404554772984461987 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (21120987141977 / 625000000000000 : ℝ) ≤ Real.sqrt (2284012021 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2284012021 / 2000000000000 : ℝ) ≤ (67587158854327 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2284012021 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau45 :
    Real.arctan (67587158854327 / 2000000000000000 : ℝ) ≤
      (337807240776056924649 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 67587158854327 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 67587158854327 : ℝ) =
              (67587158854327 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau45)
  have hz1 :
    (2000000000000000 / 67587158854327 : ℝ) ≤ 1 / Real.sqrt (2284012021 / 2000000000000 : ℝ) := by
    rw [show (2000000000000000 / 67587158854327 : ℝ) = 1 / (67587158854327 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal46 :
    (4233370302187970192887 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (21120987141977 / 46875000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (46875000000000 / 21120987141977 : ℝ) ≤
      (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (46875000000000 / 21120987141977 : ℝ) =
              (21120987141977 / 46875000000000 : ℝ)
            by
        norm_num];
        exact hal46)
  have hz2 :
    (3 / 40) / Real.sqrt (2284012021 / 2000000000000 : ℝ) ≤
      (46875000000000 / 21120987141977 : ℝ) := by
    rw [show
        (46875000000000 / 21120987141977 : ℝ) = (3 / 40) / (21120987141977 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2284012021 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2284012021 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((67587158854327 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (2284012021 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2284012021 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2284012021 / 2000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (2284012021 / 2000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_23 :
    ((6356689226027724381 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12441618812709760022989 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((44583950618293 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ))))) ≤
      Vfield (5088585351 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5088585351 / 4000000000000 : ℝ)) =
      Real.log (4005088585351 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5088585351 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (27588585351 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (6356689226027724381 / 5000000000000000000000 : ℝ) ≤
      Real.log (4005088585351 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (27588585351 / 4000000000000 : ℝ) ≤
      (-(12441618812709760022989 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (27588585351 / 4000000000000 : ℝ) = (27588585351 / 15625000000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27588585351 / 15625000000 : ℝ) ≤
            (1421324793290239977011 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (356671604946341 / 10000000000000000 : ℝ) ≤ Real.sqrt (5088585351 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5088585351 / 4000000000000 : ℝ) ≤ (44583950618293 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5088585351 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau47 :
    Real.arctan (44583950618293 / 1250000000000000 : ℝ) ≤
      (178260237063611828863 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 44583950618293 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 44583950618293 : ℝ) =
              (44583950618293 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau47)
  have hz1 :
    (1250000000000000 / 44583950618293 : ℝ) ≤ 1 / Real.sqrt (5088585351 / 4000000000000 : ℝ) := by
    rw [show (1250000000000000 / 44583950618293 : ℝ) = 1 / (44583950618293 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal48 :
    (221953446107719388427 / 500000000000000000000 : ℝ) ≤
      Real.arctan (356671604946341 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 356671604946341 : ℝ) ≤
      (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 356671604946341 : ℝ) =
              (356671604946341 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal48)
  have hz2 :
    (3 / 40) / Real.sqrt (5088585351 / 4000000000000 : ℝ) ≤
      (750000000000000 / 356671604946341 : ℝ) := by
    rw [show
        (750000000000000 / 356671604946341 : ℝ) =
          (3 / 40) / (356671604946341 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5088585351 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5088585351 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((44583950618293 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ)))) ≤
      Real.sqrt (5088585351 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5088585351 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5088585351 / 4000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (5088585351 / 4000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_24 :
    ((350326094811190417 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(49579546107330803619953 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((374471182469361 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (280457333 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (280457333 / 200000000000 : ℝ)) = Real.log (200280457333 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((280457333 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1405457333 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (350326094811190417 / 250000000000000000000 : ℝ) ≤
      Real.log (200280457333 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1405457333 / 200000000000 : ℝ) ≤
      (-(49579546107330803619953 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1405457333 / 200000000000 : ℝ) = (1405457333 / 781250000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1405457333 / 781250000 : ℝ) ≤
            (5872228316669196380047 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (187235591234679 / 5000000000000000 : ℝ) ≤ Real.sqrt (280457333 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (280457333 / 200000000000 : ℝ) ≤ (374471182469361 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (280457333 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau49 :
    Real.arctan (374471182469361 / 10000000000000000 : ℝ) ≤
      (187148145473045818201 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 374471182469361 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 374471182469361 : ℝ) =
              (374471182469361 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau49)
  have hz1 :
    (10000000000000000 / 374471182469361 : ℝ) ≤ 1 / Real.sqrt (280457333 / 200000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 374471182469361 : ℝ) = 1 / (374471182469361 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal50 :
    (4630833778944860274891 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (62411863744893 / 125000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (125000000000000 / 62411863744893 : ℝ) ≤
      (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 62411863744893 : ℝ) =
              (62411863744893 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hal50)
  have hz2 :
    (3 / 40) / Real.sqrt (280457333 / 200000000000 : ℝ) ≤
      (125000000000000 / 62411863744893 : ℝ) := by
    rw [show
        (125000000000000 / 62411863744893 : ℝ) =
          (3 / 40) / (187235591234679 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (280457333 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (280457333 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((374471182469361 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (280457333 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (280457333 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (280457333 / 200000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (280457333 / 200000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
