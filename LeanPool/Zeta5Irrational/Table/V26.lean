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

/-! # V26: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_313 :
    ((1273198027115672337129 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2437349842463477713527 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((269256675543211 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (154369229599612503803 / 625000000000000000000 : ℝ))) -
              6 * (1383821717991019276453 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (18559784275093 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18559784275093 / 64000000000000 : ℝ)) =
      Real.log (82559784275093 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18559784275093 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18919784275093 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1273198027115672337129 / 5000000000000000000000 : ℝ) ≤
      Real.log (82559784275093 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18919784275093 / 64000000000000 : ℝ) ≤
      (-(2437349842463477713527 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (18919784275093 / 64000000000000 : ℝ) = (18919784275093 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18919784275093 / 16000000000000 : ℝ) ≤
            (335238878736522286473 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (269256675543211 / 500000000000000 : ℝ) ≤ Real.sqrt (18559784275093 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18559784275093 / 64000000000000 : ℝ) ≤
      (5385133510864223 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18559784275093 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau398 :
    Real.arctan (5385133510864223 / 21357801852904144 : ℝ) ≤
      (154369229599612503803 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau397 :
    Real.arctan (5385133510864223 / 10000000000000000 : ℝ) ≤
      (2 * (154369229599612503803 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (709862615806509 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (5385133510864223 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5385133510864223 / 10000000000000000 : ℝ) /
                (1 + (709862615806509 / 625000000000000 : ℝ)) =
              (5385133510864223 / 21357801852904144 : ℝ)
            by
        norm_num];
        exact hau398)
  have hat1 :
    (Real.pi / 2 - (2 * (154369229599612503803 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5385133510864223 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5385133510864223 : ℝ) =
              (5385133510864223 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau397)
  have hz1 :
    (10000000000000000 / 5385133510864223 : ℝ) ≤
      1 / Real.sqrt (18559784275093 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5385133510864223 : ℝ) =
          1 / (5385133510864223 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (37500000000000 / 269256675543211 : ℝ) ≤
      (1383821717991019276453 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18559784275093 / 64000000000000 : ℝ) ≤
      (37500000000000 / 269256675543211 : ℝ) := by
    rw [show
        (37500000000000 / 269256675543211 : ℝ) =
          (3 / 40) / (269256675543211 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (154369229599612503803 / 625000000000000000000 : ℝ))) -
        6 * (1383821717991019276453 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18559784275093 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18559784275093 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((269256675543211 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (154369229599612503803 / 625000000000000000000 : ℝ))) -
          6 * (1383821717991019276453 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (18559784275093 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18559784275093 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18559784275093 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_314 :
    ((31888790812351289161 / 125000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6083112358839418315309 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2695384948571201 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2472091811095637514179 / 10000000000000000000000 : ℝ))) -
              6 * (691196609194341337837 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (37197312107439 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (37197312107439 / 128000000000000 : ℝ)) =
      Real.log (165197312107439 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((37197312107439 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (37917312107439 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (31888790812351289161 / 125000000000000000000 : ℝ) ≤
      Real.log (165197312107439 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (37917312107439 / 128000000000000 : ℝ) ≤
      (-(6083112358839418315309 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (37917312107439 / 128000000000000 : ℝ) = (37917312107439 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37917312107439 / 32000000000000 : ℝ) ≤
            (848359444160581684691 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2695384948571201 / 5000000000000000 : ℝ) ≤
      Real.sqrt (37197312107439 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (37197312107439 / 128000000000000 : ℝ) ≤
      (1078153979428481 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (37197312107439 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau400 :
    Real.arctan (5390769897142405 / 21360475345861928 : ℝ) ≤
      (2472091811095637514179 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau399 :
    Real.arctan (1078153979428481 / 2000000000000000 : ℝ) ≤
      (2 * (2472091811095637514179 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1420059418232741 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (1078153979428481 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1078153979428481 / 2000000000000000 : ℝ) /
                (1 + (1420059418232741 / 1250000000000000 : ℝ)) =
              (5390769897142405 / 21360475345861928 : ℝ)
            by
        norm_num];
        exact hau400)
  have hat1 :
    (Real.pi / 2 - (2 * (2472091811095637514179 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1078153979428481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1078153979428481 : ℝ) =
              (1078153979428481 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau399)
  have hz1 :
    (2000000000000000 / 1078153979428481 : ℝ) ≤
      1 / Real.sqrt (37197312107439 / 128000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1078153979428481 : ℝ) = 1 / (1078153979428481 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2695384948571201 : ℝ) ≤
      (691196609194341337837 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (37197312107439 / 128000000000000 : ℝ) ≤
      (375000000000000 / 2695384948571201 : ℝ) := by
    rw [show
        (375000000000000 / 2695384948571201 : ℝ) =
          (3 / 40) / (2695384948571201 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2472091811095637514179 / 10000000000000000000000 : ℝ))) -
        6 * (691196609194341337837 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (37197312107439 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (37197312107439 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2695384948571201 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2472091811095637514179 / 10000000000000000000000 : ℝ))) -
          6 * (691196609194341337837 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (37197312107439 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (37197312107439 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (37197312107439 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_315 :
    ((511161652200807009039 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12145742262259655687553 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5396400396379109 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (247427264076666588767 / 1000000000000000000000 : ℝ))) -
              6 * (1380969133676600751081 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9318763916173 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9318763916173 / 32000000000000 : ℝ)) =
      Real.log (41318763916173 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9318763916173 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9498763916173 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (511161652200807009039 / 2000000000000000000000 : ℝ) ≤
      Real.log (41318763916173 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9498763916173 / 32000000000000 : ℝ) ≤
      (-(12145742262259655687553 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9498763916173 / 32000000000000 : ℝ) = (9498763916173 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9498763916173 / 8000000000000 : ℝ) ≤
            (1717201343740344312447 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5396400396379109 / 10000000000000000 : ℝ) ≤ Real.sqrt (9318763916173 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9318763916173 / 32000000000000 : ℝ) ≤ (674550049547389 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9318763916173 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau402 :
    Real.arctan (5396400396379112 / 21363148209807025 : ℝ) ≤
      (247427264076666588767 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau401 :
    Real.arctan (674550049547389 / 1250000000000000 : ℝ) ≤
      (2 * (247427264076666588767 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (454525928392281 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (674550049547389 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (674550049547389 / 1250000000000000 : ℝ) /
                (1 + (454525928392281 / 400000000000000 : ℝ)) =
              (5396400396379112 / 21363148209807025 : ℝ)
            by
        norm_num];
        exact hau402)
  have hat1 :
    (Real.pi / 2 - (2 * (247427264076666588767 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 674550049547389 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 674550049547389 : ℝ) =
              (674550049547389 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau401)
  have hz1 :
    (1250000000000000 / 674550049547389 : ℝ) ≤
      1 / Real.sqrt (9318763916173 / 32000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 674550049547389 : ℝ) = 1 / (674550049547389 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5396400396379109 : ℝ) ≤
      (1380969133676600751081 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9318763916173 / 32000000000000 : ℝ) ≤
      (750000000000000 / 5396400396379109 : ℝ) := by
    rw [show
        (750000000000000 / 5396400396379109 : ℝ) =
          (3 / 40) / (5396400396379109 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (247427264076666588767 / 1000000000000000000000 : ℝ))) -
        6 * (1380969133676600751081 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9318763916173 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9318763916173 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5396400396379109 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (247427264076666588767 / 1000000000000000000000 : ℝ))) -
          6 * (1380969133676600751081 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (9318763916173 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9318763916173 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9318763916173 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_316 :
    ((1280255522181114874191 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(47364459664837705379 / 39062500000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5402025026982429 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (247645017284463756857 / 1000000000000000000000 : ℝ))) -
              6 * (689774720579922654177 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (7470559844389 / 25600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7470559844389 / 25600000000000 : ℝ)) =
      Real.log (33070559844389 / 25600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7470559844389 / 25600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7614559844389 / 25600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1280255522181114874191 / 5000000000000000000000 : ℝ) ≤
      Real.log (33070559844389 / 25600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7614559844389 / 25600000000000 : ℝ) ≤
      (-(47364459664837705379 / 39062500000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (7614559844389 / 25600000000000 : ℝ) = (7614559844389 / 6400000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7614559844389 / 6400000000000 : ℝ) ≤
            (6787663796099794621 / 39062500000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5402025026982429 / 10000000000000000 : ℝ) ≤ Real.sqrt (7470559844389 / 25600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7470559844389 / 25600000000000 : ℝ) ≤ (168813282093201 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7470559844389 / 25600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau404 :
    Real.arctan (1800675008994144 / 7121940148394401 : ℝ) ≤
      (247645017284463756857 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau403 :
    Real.arctan (168813282093201 / 312500000000000 : ℝ) ≤
      (2 * (247645017284463756857 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11365820445183203 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (168813282093201 / 312500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (168813282093201 / 312500000000000 : ℝ) /
                (1 + (11365820445183203 / 10000000000000000 : ℝ)) =
              (1800675008994144 / 7121940148394401 : ℝ)
            by
        norm_num];
        exact hau404)
  have hat1 :
    (Real.pi / 2 - (2 * (247645017284463756857 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (312500000000000 / 168813282093201 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 168813282093201 : ℝ) =
              (168813282093201 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau403)
  have hz1 :
    (312500000000000 / 168813282093201 : ℝ) ≤
      1 / Real.sqrt (7470559844389 / 25600000000000 : ℝ) := by
    rw [show (312500000000000 / 168813282093201 : ℝ) = 1 / (168813282093201 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1800675008994143 : ℝ) ≤
      (689774720579922654177 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7470559844389 / 25600000000000 : ℝ) ≤
      (250000000000000 / 1800675008994143 : ℝ) := by
    rw [show
        (250000000000000 / 1800675008994143 : ℝ) =
          (3 / 40) / (5402025026982429 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (247645017284463756857 / 1000000000000000000000 : ℝ))) -
        6 * (689774720579922654177 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7470559844389 / 25600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7470559844389 / 25600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5402025026982429 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (247645017284463756857 / 1000000000000000000000 : ℝ))) -
          6 * (689774720579922654177 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (7470559844389 / 25600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7470559844389 / 25600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7470559844389 / 25600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_317 :
    ((1282605808571419532773 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1210490278268556981051 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1081528761452943 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (619656104378955515141 / 2500000000000000000000 : ℝ))) -
              6 * (344533529576622148267 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (18715271389599 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18715271389599 / 64000000000000 : ℝ)) =
      Real.log (82715271389599 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18715271389599 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19075271389599 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1282605808571419532773 / 5000000000000000000000 : ℝ) ≤
      Real.log (82715271389599 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19075271389599 / 64000000000000 : ℝ) ≤
      (-(1210490278268556981051 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19075271389599 / 64000000000000 : ℝ) = (19075271389599 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19075271389599 / 16000000000000 : ℝ) ≤
            (175804082331443018949 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1081528761452943 / 2000000000000000 : ℝ) ≤ Real.sqrt (18715271389599 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18715271389599 / 64000000000000 : ℝ) ≤ (2703821903632359 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18715271389599 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau406 :
    Real.arctan (901273967877453 / 3561415342072285 : ℝ) ≤
      (619656104378955515141 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau405 :
    Real.arctan (2703821903632359 / 5000000000000000 : ℝ) ≤
      (2 * (619656104378955515141 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1136849205243371 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2703821903632359 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2703821903632359 / 5000000000000000 : ℝ) /
                (1 + (1136849205243371 / 1000000000000000 : ℝ)) =
              (901273967877453 / 3561415342072285 : ℝ)
            by
        norm_num];
        exact hau406)
  have hat1 :
    (Real.pi / 2 - (2 * (619656104378955515141 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2703821903632359 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2703821903632359 : ℝ) =
              (2703821903632359 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau405)
  have hz1 :
    (5000000000000000 / 2703821903632359 : ℝ) ≤
      1 / Real.sqrt (18715271389599 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2703821903632359 : ℝ) = 1 / (2703821903632359 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 360509587150981 : ℝ) ≤
      (344533529576622148267 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18715271389599 / 64000000000000 : ℝ) ≤
      (50000000000000 / 360509587150981 : ℝ) := by
    rw [show
        (50000000000000 / 360509587150981 : ℝ) =
          (3 / 40) / (1081528761452943 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (619656104378955515141 / 2500000000000000000000 : ℝ))) -
        6 * (344533529576622148267 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18715271389599 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18715271389599 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1081528761452943 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (619656104378955515141 / 2500000000000000000000 : ℝ))) -
          6 * (344533529576622148267 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (18715271389599 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18715271389599 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18715271389599 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_318 :
    ((1284954990711541413163 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6042272708977260666909 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2706628377721641 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2480795384915372937519 / 10000000000000000000000 : ℝ))) -
              6 * (43022598210815649167 / 312500000000000000000 : ℝ)))) ≤
      Vfield (37508286336451 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (37508286336451 / 128000000000000 : ℝ)) =
      Real.log (165508286336451 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((37508286336451 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (38228286336451 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1284954990711541413163 / 5000000000000000000000 : ℝ) ≤
      Real.log (165508286336451 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (38228286336451 / 128000000000000 : ℝ) ≤
      (-(6042272708977260666909 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (38228286336451 / 128000000000000 : ℝ) = (38228286336451 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38228286336451 / 32000000000000 : ℝ) ≤
            (889199094022739333091 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2706628377721641 / 5000000000000000 : ℝ) ≤
      Real.sqrt (37508286336451 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (37508286336451 / 128000000000000 : ℝ) ≤
      (1082651351088657 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (37508286336451 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau408 :
    Real.arctan (360883783696219 / 1424744202133418 : ℝ) ≤
      (2480795384915372937519 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau407 :
    Real.arctan (1082651351088657 / 2000000000000000 : ℝ) ≤
      (2 * (2480795384915372937519 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1137116303200127 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1082651351088657 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1082651351088657 / 2000000000000000 : ℝ) /
                (1 + (1137116303200127 / 1000000000000000 : ℝ)) =
              (360883783696219 / 1424744202133418 : ℝ)
            by
        norm_num];
        exact hau408)
  have hat1 :
    (Real.pi / 2 - (2 * (2480795384915372937519 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1082651351088657 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1082651351088657 : ℝ) =
              (1082651351088657 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau407)
  have hz1 :
    (2000000000000000 / 1082651351088657 : ℝ) ≤
      1 / Real.sqrt (37508286336451 / 128000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1082651351088657 : ℝ) = 1 / (1082651351088657 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 902209459240547 : ℝ) ≤
      (43022598210815649167 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (37508286336451 / 128000000000000 : ℝ) ≤
      (125000000000000 / 902209459240547 : ℝ) := by
    rw [show
        (125000000000000 / 902209459240547 : ℝ) =
          (3 / 40) / (2706628377721641 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2480795384915372937519 / 10000000000000000000000 : ℝ))) -
        6 * (43022598210815649167 / 312500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (37508286336451 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (37508286336451 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2706628377721641 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2480795384915372937519 / 10000000000000000000000 : ℝ))) -
          6 * (43022598210815649167 / 312500000000000000000 : ℝ))) ≤
      Real.sqrt (37508286336451 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (37508286336451 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (37508286336451 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_319 :
    ((20114110463103549801 / 78125000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12064229411273515284231 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5418863889641097 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (496592617025537929121 / 2000000000000000000000 : ℝ))) -
              6 * (275063298453652888357 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (4698253736713 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4698253736713 / 16000000000000 : ℝ)) =
      Real.log (20698253736713 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4698253736713 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4788253736713 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (20114110463103549801 / 78125000000000000000 : ℝ) ≤
      Real.log (20698253736713 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4788253736713 / 16000000000000 : ℝ) ≤
      (-(12064229411273515284231 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4788253736713 / 16000000000000 : ℝ) = (4788253736713 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4788253736713 / 4000000000000 : ℝ) ≤
            (1798714194726484715769 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5418863889641097 / 10000000000000000 : ℝ) ≤ Real.sqrt (4698253736713 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4698253736713 / 16000000000000 : ℝ) ≤ (54188638896411 / 100000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4698253736713 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau410 :
    Real.arctan (5418863889641100 / 21373833384328093 : ℝ) ≤
      (496592617025537929121 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau409 :
    Real.arctan (54188638896411 / 100000000000000 : ℝ) ≤
      (2 * (496592617025537929121 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11373833384328093 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (54188638896411 / 100000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (54188638896411 / 100000000000000 : ℝ) /
                (1 + (11373833384328093 / 10000000000000000 : ℝ)) =
              (5418863889641100 / 21373833384328093 : ℝ)
            by
        norm_num];
        exact hau410)
  have hat1 :
    (Real.pi / 2 - (2 * (496592617025537929121 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (100000000000000 / 54188638896411 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (100000000000000 / 54188638896411 : ℝ) =
              (54188638896411 / 100000000000000 : ℝ)
            by
        norm_num];
        exact hau409)
  have hz1 :
    (100000000000000 / 54188638896411 : ℝ) ≤ 1 / Real.sqrt (4698253736713 / 16000000000000 : ℝ) :=
  by
    rw [show (100000000000000 / 54188638896411 : ℝ) = 1 / (54188638896411 / 100000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1806287963213699 : ℝ) ≤
      (275063298453652888357 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4698253736713 / 16000000000000 : ℝ) ≤
      (250000000000000 / 1806287963213699 : ℝ) := by
    rw [show
        (250000000000000 / 1806287963213699 : ℝ) =
          (3 / 40) / (5418863889641097 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (496592617025537929121 / 2000000000000000000000 : ℝ))) -
        6 * (275063298453652888357 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4698253736713 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4698253736713 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5418863889641097 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (496592617025537929121 / 2000000000000000000000 : ℝ))) -
          6 * (275063298453652888357 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (4698253736713 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4698253736713 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4698253736713 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_320 :
    ((2579300092776726062851 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3010988648734265671267 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5424465227887459 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (310640941023347092163 / 1250000000000000000000 : ℝ))) -
              6 * (1373914144821106679677 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (37663773450957 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (37663773450957 / 128000000000000 : ℝ)) =
      Real.log (165663773450957 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((37663773450957 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (38383773450957 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2579300092776726062851 / 10000000000000000000000 : ℝ) ≤
      Real.log (165663773450957 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (38383773450957 / 128000000000000 : ℝ) ≤
      (-(3010988648734265671267 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (38383773450957 / 128000000000000 : ℝ) = (38383773450957 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38383773450957 / 32000000000000 : ℝ) ≤
            (454747252765734328733 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5424465227887459 / 10000000000000000 : ℝ) ≤
      Real.sqrt (37663773450957 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (37663773450957 / 128000000000000 : ℝ) ≤
      (2712232613943731 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (37663773450957 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau412 :
    Real.arctan (2712232613943731 / 10688251554927932 : ℝ) ≤
      (310640941023347092163 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau411 :
    Real.arctan (2712232613943731 / 5000000000000000 : ℝ) ≤
      (2 * (310640941023347092163 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1422062888731983 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (2712232613943731 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2712232613943731 / 5000000000000000 : ℝ) /
                (1 + (1422062888731983 / 1250000000000000 : ℝ)) =
              (2712232613943731 / 10688251554927932 : ℝ)
            by
        norm_num];
        exact hau412)
  have hat1 :
    (Real.pi / 2 - (2 * (310640941023347092163 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2712232613943731 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2712232613943731 : ℝ) =
              (2712232613943731 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau411)
  have hz1 :
    (5000000000000000 / 2712232613943731 : ℝ) ≤
      1 / Real.sqrt (37663773450957 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2712232613943731 : ℝ) = 1 / (2712232613943731 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5424465227887459 : ℝ) ≤
      (1373914144821106679677 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (37663773450957 / 128000000000000 : ℝ) ≤
      (750000000000000 / 5424465227887459 : ℝ) := by
    rw [show
        (750000000000000 / 5424465227887459 : ℝ) =
          (3 / 40) / (5424465227887459 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (310640941023347092163 / 1250000000000000000000 : ℝ))) -
        6 * (1373914144821106679677 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (37663773450957 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (37663773450957 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5424465227887459 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (310640941023347092163 / 1250000000000000000000 : ℝ))) -
          6 * (1373914144821106679677 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (37663773450957 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (37663773450957 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (37663773450957 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_321 :
    ((645997960997488683677 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12023720802257671034363 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5430060788118679 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (621822181019150037887 / 2500000000000000000000 : ℝ))) -
              6 * (1372516078509845972423 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3774151700821 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3774151700821 / 12800000000000 : ℝ)) =
      Real.log (16574151700821 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3774151700821 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3846151700821 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (645997960997488683677 / 2500000000000000000000 : ℝ) ≤
      Real.log (16574151700821 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3846151700821 / 12800000000000 : ℝ) ≤
      (-(12023720802257671034363 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (3846151700821 / 12800000000000 : ℝ) = (3846151700821 / 3200000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3846151700821 / 3200000000000 : ℝ) ≤
            (1839222803742328965637 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5430060788118679 / 10000000000000000 : ℝ) ≤ Real.sqrt (3774151700821 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3774151700821 / 12800000000000 : ℝ) ≤ (2715030394059341 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3774151700821 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau414 :
    Real.arctan (2715030394059341 / 10689586104512877 : ℝ) ≤
      (621822181019150037887 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau413 :
    Real.arctan (2715030394059341 / 5000000000000000 : ℝ) ≤
      (2 * (621822181019150037887 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5689586104512877 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2715030394059341 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2715030394059341 / 5000000000000000 : ℝ) /
                (1 + (5689586104512877 / 5000000000000000 : ℝ)) =
              (2715030394059341 / 10689586104512877 : ℝ)
            by
        norm_num];
        exact hau414)
  have hat1 :
    (Real.pi / 2 - (2 * (621822181019150037887 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2715030394059341 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2715030394059341 : ℝ) =
              (2715030394059341 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau413)
  have hz1 :
    (5000000000000000 / 2715030394059341 : ℝ) ≤
      1 / Real.sqrt (3774151700821 / 12800000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2715030394059341 : ℝ) = 1 / (2715030394059341 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5430060788118679 : ℝ) ≤
      (1372516078509845972423 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3774151700821 / 12800000000000 : ℝ) ≤
      (750000000000000 / 5430060788118679 : ℝ) := by
    rw [show
        (750000000000000 / 5430060788118679 : ℝ) =
          (3 / 40) / (5430060788118679 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (621822181019150037887 / 2500000000000000000000 : ℝ))) -
        6 * (1372516078509845972423 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3774151700821 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3774151700821 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5430060788118679 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (621822181019150037887 / 2500000000000000000000 : ℝ))) -
          6 * (1372516078509845972423 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3774151700821 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3774151700821 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3774151700821 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_322 :
    ((647170348745621798299 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(120035278675576217591 / 100000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2717825294089373 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (248944668273143873453 / 1000000000000000000000 : ℝ))) -
              6 * (1371122271595357286801 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (37819260565463 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (37819260565463 / 128000000000000 : ℝ)) =
      Real.log (165819260565463 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((37819260565463 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (38539260565463 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (647170348745621798299 / 2500000000000000000000 : ℝ) ≤
      Real.log (165819260565463 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (38539260565463 / 128000000000000 : ℝ) ≤
      (-(120035278675576217591 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (38539260565463 / 128000000000000 : ℝ) = (38539260565463 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38539260565463 / 32000000000000 : ℝ) ≤
            (18594157384423782409 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2717825294089373 / 5000000000000000 : ℝ) ≤
      Real.sqrt (37819260565463 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (37819260565463 / 128000000000000 : ℝ) ≤
      (5435650588178749 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (37819260565463 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau416 :
    Real.arctan (5435650588178749 / 21381840682278414 : ℝ) ≤
      (248944668273143873453 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau415 :
    Real.arctan (5435650588178749 / 10000000000000000 : ℝ) ≤
      (2 * (248944668273143873453 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5690920341139207 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5435650588178749 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5435650588178749 / 10000000000000000 : ℝ) /
                (1 + (5690920341139207 / 5000000000000000 : ℝ)) =
              (5435650588178749 / 21381840682278414 : ℝ)
            by
        norm_num];
        exact hau416)
  have hat1 :
    (Real.pi / 2 - (2 * (248944668273143873453 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5435650588178749 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5435650588178749 : ℝ) =
              (5435650588178749 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau415)
  have hz1 :
    (10000000000000000 / 5435650588178749 : ℝ) ≤
      1 / Real.sqrt (37819260565463 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5435650588178749 : ℝ) =
          1 / (5435650588178749 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2717825294089373 : ℝ) ≤
      (1371122271595357286801 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (37819260565463 / 128000000000000 : ℝ) ≤
      (375000000000000 / 2717825294089373 : ℝ) := by
    rw [show
        (375000000000000 / 2717825294089373 : ℝ) =
          (3 / 40) / (2717825294089373 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (248944668273143873453 / 1000000000000000000000 : ℝ))) -
        6 * (1371122271595357286801 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (37819260565463 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (37819260565463 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2717825294089373 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (248944668273143873453 / 1000000000000000000000 : ℝ))) -
          6 * (1371122271595357286801 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (37819260565463 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (37819260565463 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (37819260565463 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_323 :
    ((518673749563393131451 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5991687813080415260473 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1360308661454999 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2491601414036235246563 / 10000000000000000000000 : ℝ))) -
              6 * (684866351246375430211 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9474251030679 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9474251030679 / 32000000000000 : ℝ)) =
      Real.log (41474251030679 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9474251030679 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9654251030679 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (518673749563393131451 / 2000000000000000000000 : ℝ) ≤
      Real.log (41474251030679 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9654251030679 / 32000000000000 : ℝ) ≤
      (-(5991687813080415260473 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9654251030679 / 32000000000000 : ℝ) = (9654251030679 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9654251030679 / 8000000000000 : ℝ) ≤
            (939783989919584739527 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1360308661454999 / 2500000000000000 : ℝ) ≤ Real.sqrt (9474251030679 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9474251030679 / 32000000000000 : ℝ) ≤ (5441234645819999 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9474251030679 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau418 :
    Real.arctan (418556511216923 / 1644962194619537 : ℝ) ≤
      (2491601414036235246563 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau417 :
    Real.arctan (5441234645819999 / 10000000000000000 : ℝ) ≤
      (2 * (2491601414036235246563 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11384508530053981 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5441234645819999 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5441234645819999 / 10000000000000000 : ℝ) /
                (1 + (11384508530053981 / 10000000000000000 : ℝ)) =
              (418556511216923 / 1644962194619537 : ℝ)
            by
        norm_num];
        exact hau418)
  have hat1 :
    (Real.pi / 2 - (2 * (2491601414036235246563 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5441234645819999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5441234645819999 : ℝ) =
              (5441234645819999 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau417)
  have hz1 :
    (10000000000000000 / 5441234645819999 : ℝ) ≤
      1 / Real.sqrt (9474251030679 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5441234645819999 : ℝ) =
          1 / (5441234645819999 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1360308661454999 : ℝ) ≤
      (684866351246375430211 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9474251030679 / 32000000000000 : ℝ) ≤
      (187500000000000 / 1360308661454999 : ℝ) := by
    rw [show
        (187500000000000 / 1360308661454999 : ℝ) =
          (3 / 40) / (1360308661454999 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2491601414036235246563 / 10000000000000000000000 : ℝ))) -
        6 * (684866351246375430211 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9474251030679 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9474251030679 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1360308661454999 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2491601414036235246563 / 10000000000000000000000 : ℝ))) -
          6 * (684866351246375430211 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9474251030679 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9474251030679 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9474251030679 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_324 :
    ((1299026952276566602519 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11963263914384789373721 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1361703244675941 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2493752927826940413923 / 10000000000000000000000 : ℝ))) -
              6 * (1368347349769969504417 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (37974747679969 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (37974747679969 / 128000000000000 : ℝ)) =
      Real.log (165974747679969 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((37974747679969 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (38694747679969 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1299026952276566602519 / 5000000000000000000000 : ℝ) ≤
      Real.log (165974747679969 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (38694747679969 / 128000000000000 : ℝ) ≤
      (-(11963263914384789373721 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (38694747679969 / 128000000000000 : ℝ) = (38694747679969 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38694747679969 / 32000000000000 : ℝ) ≤
            (1899679691615210626279 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1361703244675941 / 2500000000000000 : ℝ) ≤
      Real.sqrt (37974747679969 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (37974747679969 / 128000000000000 : ℝ) ≤
      (5446812978703767 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (37974747679969 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau420 :
    Real.arctan (1815604326234589 / 7129058584264025 : ℝ) ≤
      (2493752927826940413923 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau419 :
    Real.arctan (5446812978703767 / 10000000000000000 : ℝ) ≤
      (2 * (2493752927826940413923 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (455487030111683 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (5446812978703767 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5446812978703767 / 10000000000000000 : ℝ) /
                (1 + (455487030111683 / 400000000000000 : ℝ)) =
              (1815604326234589 / 7129058584264025 : ℝ)
            by
        norm_num];
        exact hau420)
  have hat1 :
    (Real.pi / 2 - (2 * (2493752927826940413923 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5446812978703767 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5446812978703767 : ℝ) =
              (5446812978703767 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau419)
  have hz1 :
    (10000000000000000 / 5446812978703767 : ℝ) ≤
      1 / Real.sqrt (37974747679969 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5446812978703767 : ℝ) =
          1 / (5446812978703767 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 453901081558647 : ℝ) ≤
      (1368347349769969504417 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (37974747679969 / 128000000000000 : ℝ) ≤
      (62500000000000 / 453901081558647 : ℝ) := by
    rw [show
        (62500000000000 / 453901081558647 : ℝ) =
          (3 / 40) / (1361703244675941 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2493752927826940413923 / 10000000000000000000000 : ℝ))) -
        6 * (1368347349769969504417 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (37974747679969 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (37974747679969 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1361703244675941 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2493752927826940413923 / 10000000000000000000000 : ℝ))) -
          6 * (1368347349769969504417 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (37974747679969 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (37974747679969 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (37974747679969 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
