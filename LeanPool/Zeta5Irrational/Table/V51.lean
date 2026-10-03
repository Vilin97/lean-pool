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

/-! # V51: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_613 :
    ((5372493143715501039287 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(332793597066236323861 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1054227466493001 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1751598472914581166259 / 5000000000000000000000 : ℝ))) -
              6 * (886943661285501435459 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22761380886697 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22761380886697 / 32000000000000 : ℝ)) =
      Real.log (54761380886697 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22761380886697 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22941380886697 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5372493143715501039287 / 10000000000000000000000 : ℝ) ≤
      Real.log (54761380886697 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22941380886697 / 32000000000000 : ℝ) ≤
      (-(332793597066236323861 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22941380886697 / 32000000000000 : ℝ) = (22941380886697 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22941380886697 / 16000000000000 : ℝ) ≤
            (360353583233763676139 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1054227466493001 / 1250000000000000 : ℝ) ≤ Real.sqrt (22761380886697 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22761380886697 / 32000000000000 : ℝ) ≤
      (8433819731944011 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22761380886697 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau998 :
    Real.arctan (2811273243981337 / 7693880129715234 : ℝ) ≤
      (1751598472914581166259 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau997 :
    Real.arctan (8433819731944011 / 10000000000000000 : ℝ) ≤
      (2 * (1751598472914581166259 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6540820194572851 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8433819731944011 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8433819731944011 / 10000000000000000 : ℝ) /
                (1 + (6540820194572851 / 5000000000000000 : ℝ)) =
              (2811273243981337 / 7693880129715234 : ℝ)
            by
        norm_num];
        exact hau998)
  have hat1 :
    (Real.pi / 2 - (2 * (1751598472914581166259 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8433819731944011 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8433819731944011 : ℝ) =
              (8433819731944011 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau997)
  have hz1 :
    (10000000000000000 / 8433819731944011 : ℝ) ≤
      1 / Real.sqrt (22761380886697 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8433819731944011 : ℝ) =
          1 / (8433819731944011 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 351409155497667 : ℝ) ≤
      (886943661285501435459 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22761380886697 / 32000000000000 : ℝ) ≤
      (31250000000000 / 351409155497667 : ℝ) := by
    rw [show
        (31250000000000 / 351409155497667 : ℝ) =
          (3 / 40) / (1054227466493001 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1751598472914581166259 / 5000000000000000000000 : ℝ))) -
        6 * (886943661285501435459 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22761380886697 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22761380886697 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1054227466493001 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1751598472914581166259 / 5000000000000000000000 : ℝ))) -
          6 * (886943661285501435459 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22761380886697 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22761380886697 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22761380886697 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_614 :
    ((5381969639025595980783 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1652665149511791927237 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1688686622805057 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (876501105435104276007 / 2500000000000000000000 : ℝ))) -
              6 * (885939098663711472987 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11406650040163 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11406650040163 / 16000000000000 : ℝ)) =
      Real.log (27406650040163 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11406650040163 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11496650040163 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5381969639025595980783 / 10000000000000000000000 : ℝ) ≤
      Real.log (27406650040163 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11496650040163 / 16000000000000 : ℝ) ≤
      (-(1652665149511791927237 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11496650040163 / 16000000000000 : ℝ) = (11496650040163 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11496650040163 / 8000000000000 : ℝ) ≤
            (1813070751988208072763 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1688686622805057 / 2000000000000000 : ℝ) ≤ Real.sqrt (11406650040163 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11406650040163 / 16000000000000 : ℝ) ≤ (1055429139253161 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11406650040163 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1000 :
    Real.arctan (4221716557012644 / 11543920131523205 : ℝ) ≤
      (876501105435104276007 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau999 :
    Real.arctan (1055429139253161 / 1250000000000000 : ℝ) ≤
      (2 * (876501105435104276007 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1308784026304641 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1055429139253161 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1055429139253161 / 1250000000000000 : ℝ) /
                (1 + (1308784026304641 / 1000000000000000 : ℝ)) =
              (4221716557012644 / 11543920131523205 : ℝ)
            by
        norm_num];
        exact hau1000)
  have hat1 :
    (Real.pi / 2 - (2 * (876501105435104276007 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 1055429139253161 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 1055429139253161 : ℝ) =
              (1055429139253161 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau999)
  have hz1 :
    (1250000000000000 / 1055429139253161 : ℝ) ≤
      1 / Real.sqrt (11406650040163 / 16000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 1055429139253161 : ℝ) = 1 / (1055429139253161 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 562895540935019 : ℝ) ≤
      (885939098663711472987 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11406650040163 / 16000000000000 : ℝ) ≤
      (50000000000000 / 562895540935019 : ℝ) := by
    rw [show
        (50000000000000 / 562895540935019 : ℝ) =
          (3 / 40) / (1688686622805057 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (876501105435104276007 / 2500000000000000000000 : ℝ))) -
        6 * (885939098663711472987 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11406650040163 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11406650040163 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1688686622805057 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (876501105435104276007 / 2500000000000000000000 : ℝ))) -
          6 * (885939098663711472987 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (11406650040163 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11406650040163 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11406650040163 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_615 :
    ((5400895730933659307041 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(815067921368615468109 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((846262711639831 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1755800926009630248063 / 5000000000000000000000 : ℝ))) -
              6 * (88394017114811751033 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (89520072139 / 125000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (89520072139 / 125000000000 : ℝ)) =
      Real.log (214520072139 / 125000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((89520072139 / 125000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (90223197139 / 125000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5400895730933659307041 / 10000000000000000000000 : ℝ) ≤
      Real.log (214520072139 / 125000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (90223197139 / 125000000000 : ℝ) ≤
      (-(815067921368615468109 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (90223197139 / 125000000000 : ℝ) = (90223197139 / 62500000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (90223197139 / 62500000000 : ℝ) ≤
            (917800029381384531891 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (846262711639831 / 1000000000000000 : ℝ) ≤ Real.sqrt (89520072139 / 125000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (89520072139 / 125000000000 : ℝ) ≤ (8462627116398313 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (89520072139 / 125000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau1002 :
    Real.arctan (8462627116398313 / 23100231208310790 : ℝ) ≤
      (1755800926009630248063 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1001 :
    Real.arctan (8462627116398313 / 10000000000000000 : ℝ) ≤
      (2 * (1755800926009630248063 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1310023120831079 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8462627116398313 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8462627116398313 / 10000000000000000 : ℝ) /
                (1 + (1310023120831079 / 1000000000000000 : ℝ)) =
              (8462627116398313 / 23100231208310790 : ℝ)
            by
        norm_num];
        exact hau1002)
  have hat1 :
    (Real.pi / 2 - (2 * (1755800926009630248063 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8462627116398313 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8462627116398313 : ℝ) =
              (8462627116398313 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1001)
  have hz1 :
    (10000000000000000 / 8462627116398313 : ℝ) ≤ 1 / Real.sqrt (89520072139 / 125000000000 : ℝ) :=
  by
    rw [show
        (10000000000000000 / 8462627116398313 : ℝ) =
          1 / (8462627116398313 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 846262711639831 : ℝ) ≤
      (88394017114811751033 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (89520072139 / 125000000000 : ℝ) ≤
      (75000000000000 / 846262711639831 : ℝ) := by
    rw [show
        (75000000000000 / 846262711639831 : ℝ) =
          (3 / 40) / (846262711639831 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1755800926009630248063 / 5000000000000000000000 : ℝ))) -
        6 * (88394017114811751033 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (89520072139 / 125000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (89520072139 / 125000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((846262711639831 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1755800926009630248063 / 5000000000000000000000 : ℝ))) -
          6 * (88394017114811751033 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (89520072139 / 125000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (89520072139 / 125000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (89520072139 / 125000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_616 :
    ((216479549629272587089 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(808479101909136909281 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8473873801407549 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3514876734834164438587 / 10000000000000000000000 : ℝ))) -
              6 * (17655461571844476817 / 200000000000000000000 : ℝ)))) ≤
      Vfield (11489045952349 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11489045952349 / 16000000000000 : ℝ)) =
      Real.log (27489045952349 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11489045952349 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11579045952349 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (216479549629272587089 / 400000000000000000000 : ℝ) ≤
      Real.log (27489045952349 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11579045952349 / 16000000000000 : ℝ) ≤
      (-(808479101909136909281 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11579045952349 / 16000000000000 : ℝ) = (11579045952349 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11579045952349 / 8000000000000 : ℝ) ≤
            (924388848840863090719 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8473873801407549 / 10000000000000000 : ℝ) ≤
      Real.sqrt (11489045952349 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11489045952349 / 16000000000000 : ℝ) ≤ (132404278146993 / 156250000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11489045952349 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1004 :
    Real.arctan (8473873801407552 / 23107499273399989 : ℝ) ≤
      (3514876734834164438587 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1003 :
    Real.arctan (132404278146993 / 156250000000000 : ℝ) ≤
      (2 * (3514876734834164438587 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13107499273399989 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (132404278146993 / 156250000000000 : ℝ) ^ 2))
      (by
        rw [show
            (132404278146993 / 156250000000000 : ℝ) /
                (1 + (13107499273399989 / 10000000000000000 : ℝ)) =
              (8473873801407552 / 23107499273399989 : ℝ)
            by
        norm_num];
        exact hau1004)
  have hat1 :
    (Real.pi / 2 - (2 * (3514876734834164438587 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (156250000000000 / 132404278146993 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (156250000000000 / 132404278146993 : ℝ) =
              (132404278146993 / 156250000000000 : ℝ)
            by
        norm_num];
        exact hau1003)
  have hz1 :
    (156250000000000 / 132404278146993 : ℝ) ≤
      1 / Real.sqrt (11489045952349 / 16000000000000 : ℝ) := by
    rw [show (156250000000000 / 132404278146993 : ℝ) = 1 / (132404278146993 / 156250000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2824624600469183 : ℝ) ≤
      (17655461571844476817 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11489045952349 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2824624600469183 : ℝ) := by
    rw [show
        (250000000000000 / 2824624600469183 : ℝ) =
          (3 / 40) / (8473873801407549 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3514876734834164438587 / 10000000000000000000000 : ℝ))) -
        6 * (17655461571844476817 / 200000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11489045952349 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11489045952349 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8473873801407549 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3514876734834164438587 / 10000000000000000000000 : ℝ))) -
          6 * (17655461571844476817 / 200000000000000000000 : ℝ))) ≤
      Real.sqrt (11489045952349 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11489045952349 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11489045952349 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_617 :
    ((2708765317241712306349 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3220764770559494080803 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8479491550067837 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3516511187288392257217 / 10000000000000000000000 : ℝ))) -
              6 * (882191263222842597187 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4601713724651 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4601713724651 / 6400000000000 : ℝ)) =
      Real.log (11001713724651 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4601713724651 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4637713724651 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2708765317241712306349 / 5000000000000000000000 : ℝ) ≤
      Real.log (11001713724651 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4637713724651 / 6400000000000 : ℝ) ≤
      (-(3220764770559494080803 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4637713724651 / 6400000000000 : ℝ) = (4637713724651 / 3200000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4637713724651 / 3200000000000 : ℝ) ≤
            (3710707032440505919197 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8479491550067837 / 10000000000000000 : ℝ) ≤ Real.sqrt (4601713724651 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4601713724651 / 6400000000000 : ℝ) ≤ (13249205546981 / 15625000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4601713724651 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1006 :
    Real.arctan (8479491550067840 / 23111131795069099 : ℝ) ≤
      (3516511187288392257217 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1005 :
    Real.arctan (13249205546981 / 15625000000000 : ℝ) ≤
      (2 * (3516511187288392257217 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13111131795069099 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (13249205546981 / 15625000000000 : ℝ) ^ 2))
      (by
        rw [show
            (13249205546981 / 15625000000000 : ℝ) /
                (1 + (13111131795069099 / 10000000000000000 : ℝ)) =
              (8479491550067840 / 23111131795069099 : ℝ)
            by
        norm_num];
        exact hau1006)
  have hat1 :
    (Real.pi / 2 - (2 * (3516511187288392257217 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (15625000000000 / 13249205546981 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (15625000000000 / 13249205546981 : ℝ) =
              (13249205546981 / 15625000000000 : ℝ)
            by
        norm_num];
        exact hau1005)
  have hz1 :
    (15625000000000 / 13249205546981 : ℝ) ≤ 1 / Real.sqrt (4601713724651 / 6400000000000 : ℝ) := by
    rw [show (15625000000000 / 13249205546981 : ℝ) = 1 / (13249205546981 / 15625000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8479491550067837 : ℝ) ≤
      (882191263222842597187 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4601713724651 / 6400000000000 : ℝ) ≤
      (750000000000000 / 8479491550067837 : ℝ) := by
    rw [show
        (750000000000000 / 8479491550067837 : ℝ) =
          (3 / 40) / (8479491550067837 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3516511187288392257217 / 10000000000000000000000 : ℝ))) -
        6 * (882191263222842597187 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4601713724651 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4601713724651 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8479491550067837 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3516511187288392257217 / 10000000000000000000000 : ℝ))) -
          6 * (882191263222842597187 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4601713724651 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4601713724651 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4601713724651 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_618 :
    ((2711534729338718410971 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1603815203661389908143 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((212127639484407 / 250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (439767956615355164713 / 1250000000000000000000 : ℝ))) -
              6 * (881610596728614691281 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5759761335453 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5759761335453 / 8000000000000 : ℝ)) =
      Real.log (13759761335453 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5759761335453 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5804761335453 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2711534729338718410971 / 5000000000000000000000 : ℝ) ≤
      Real.log (13759761335453 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5804761335453 / 8000000000000 : ℝ) ≤
      (-(1603815203661389908143 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5804761335453 / 8000000000000 : ℝ) = (5804761335453 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5804761335453 / 4000000000000 : ℝ) ≤
            (1861920697838610091857 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (212127639484407 / 250000000000000 : ℝ) ≤ Real.sqrt (5759761335453 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5759761335453 / 8000000000000 : ℝ) ≤ (8485105579376283 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5759761335453 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1008 :
    Real.arctan (8485105579376283 / 23114763310603912 : ℝ) ≤
      (439767956615355164713 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1007 :
    Real.arctan (8485105579376283 / 10000000000000000 : ℝ) ≤
      (2 * (439767956615355164713 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1639345413825489 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (8485105579376283 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8485105579376283 / 10000000000000000 : ℝ) /
                (1 + (1639345413825489 / 1250000000000000 : ℝ)) =
              (8485105579376283 / 23114763310603912 : ℝ)
            by
        norm_num];
        exact hau1008)
  have hat1 :
    (Real.pi / 2 - (2 * (439767956615355164713 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8485105579376283 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8485105579376283 : ℝ) =
              (8485105579376283 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1007)
  have hz1 :
    (10000000000000000 / 8485105579376283 : ℝ) ≤
      1 / Real.sqrt (5759761335453 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8485105579376283 : ℝ) =
          1 / (8485105579376283 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (6250000000000 / 70709213161469 : ℝ) ≤
      (881610596728614691281 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5759761335453 / 8000000000000 : ℝ) ≤
      (6250000000000 / 70709213161469 : ℝ) := by
    rw [show
        (6250000000000 / 70709213161469 : ℝ) = (3 / 40) / (212127639484407 / 250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (439767956615355164713 / 1250000000000000000000 : ℝ))) -
        6 * (881610596728614691281 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5759761335453 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5759761335453 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((212127639484407 / 250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (439767956615355164713 / 1250000000000000000000 : ℝ))) -
          6 * (881610596728614691281 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5759761335453 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5759761335453 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5759761335453 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_619 :
    ((1085721043342463421133 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3194513272609733674267 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4245357948355271 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3519774136081336267697 / 10000000000000000000000 : ℝ))) -
              6 * (22025776883336704059 / 250000000000000000000 : ℝ)))) ≤
      Vfield (23069522060369 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23069522060369 / 32000000000000 : ℝ)) =
      Real.log (55069522060369 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23069522060369 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23249522060369 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1085721043342463421133 / 2000000000000000000000 : ℝ) ≤
      Real.log (55069522060369 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23249522060369 / 32000000000000 : ℝ) ≤
      (-(3194513272609733674267 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23249522060369 / 32000000000000 : ℝ) = (23249522060369 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23249522060369 / 16000000000000 : ℝ) ≤
            (3736958530390266325733 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4245357948355271 / 5000000000000000 : ℝ) ≤ Real.sqrt (23069522060369 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23069522060369 / 32000000000000 : ℝ) ≤ (1698143179342109 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23069522060369 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1010 :
    Real.arctan (8490715896710545 / 23118393820840001 : ℝ) ≤
      (3519774136081336267697 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1009 :
    Real.arctan (1698143179342109 / 2000000000000000 : ℝ) ≤
      (2 * (3519774136081336267697 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13118393820840001 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1698143179342109 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1698143179342109 / 2000000000000000 : ℝ) /
                (1 + (13118393820840001 / 10000000000000000 : ℝ)) =
              (8490715896710545 / 23118393820840001 : ℝ)
            by
        norm_num];
        exact hau1010)
  have hat1 :
    (Real.pi / 2 - (2 * (3519774136081336267697 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1698143179342109 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1698143179342109 : ℝ) =
              (1698143179342109 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1009)
  have hz1 :
    (2000000000000000 / 1698143179342109 : ℝ) ≤
      1 / Real.sqrt (23069522060369 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1698143179342109 : ℝ) = 1 / (1698143179342109 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4245357948355271 : ℝ) ≤
      (22025776883336704059 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23069522060369 / 32000000000000 : ℝ) ≤
      (375000000000000 / 4245357948355271 : ℝ) := by
    rw [show
        (375000000000000 / 4245357948355271 : ℝ) =
          (3 / 40) / (4245357948355271 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3519774136081336267697 / 10000000000000000000000 : ℝ))) -
        6 * (22025776883336704059 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23069522060369 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23069522060369 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4245357948355271 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3519774136081336267697 / 10000000000000000000000 : ℝ))) -
          6 * (22025776883336704059 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (23069522060369 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23069522060369 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23069522060369 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_620 :
    ((2717068955990445230723 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3181413321281778418051 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8496322509423929 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (176070132054670847363 / 500000000000000000000 : ℝ))) -
              6 * (440226347639341872671 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (11549999389463 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11549999389463 / 16000000000000 : ℝ)) =
      Real.log (27549999389463 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11549999389463 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11639999389463 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2717068955990445230723 / 5000000000000000000000 : ℝ) ≤
      Real.log (27549999389463 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11639999389463 / 16000000000000 : ℝ) ≤
      (-(3181413321281778418051 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11639999389463 / 16000000000000 : ℝ) = (11639999389463 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11639999389463 / 8000000000000 : ℝ) ≤
            (3750058481718221581949 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8496322509423929 / 10000000000000000 : ℝ) ≤
      Real.sqrt (11549999389463 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11549999389463 / 16000000000000 : ℝ) ≤ (2124080627355983 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11549999389463 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1012 :
    Real.arctan (4248161254711966 / 11561011663305891 : ℝ) ≤
      (176070132054670847363 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1011 :
    Real.arctan (2124080627355983 / 2500000000000000 : ℝ) ≤
      (2 * (176070132054670847363 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6561011663305891 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2124080627355983 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2124080627355983 / 2500000000000000 : ℝ) /
                (1 + (6561011663305891 / 5000000000000000 : ℝ)) =
              (4248161254711966 / 11561011663305891 : ℝ)
            by
        norm_num];
        exact hau1012)
  have hat1 :
    (Real.pi / 2 - (2 * (176070132054670847363 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2124080627355983 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2124080627355983 : ℝ) =
              (2124080627355983 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1011)
  have hz1 :
    (2500000000000000 / 2124080627355983 : ℝ) ≤
      1 / Real.sqrt (11549999389463 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2124080627355983 : ℝ) = 1 / (2124080627355983 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8496322509423929 : ℝ) ≤
      (440226347639341872671 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11549999389463 / 16000000000000 : ℝ) ≤
      (750000000000000 / 8496322509423929 : ℝ) := by
    rw [show
        (750000000000000 / 8496322509423929 : ℝ) =
          (3 / 40) / (8496322509423929 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (176070132054670847363 / 500000000000000000000 : ℝ))) -
        6 * (440226347639341872671 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11549999389463 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11549999389463 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8496322509423929 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (176070132054670847363 / 500000000000000000000 : ℝ))) -
          6 * (440226347639341872671 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (11549999389463 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11549999389463 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11549999389463 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_621 :
    ((543966754787035356037 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3168330508377498755171 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8501925424845501 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (220189323267150120757 / 625000000000000000000 : ℝ))) -
              6 * (439937726411396261549 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (23130475497483 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23130475497483 / 32000000000000 : ℝ)) =
      Real.log (55130475497483 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23130475497483 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23310475497483 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (543966754787035356037 / 1000000000000000000000 : ℝ) ≤
      Real.log (55130475497483 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23310475497483 / 32000000000000 : ℝ) ≤
      (-(3168330508377498755171 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23310475497483 / 32000000000000 : ℝ) = (23310475497483 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23310475497483 / 16000000000000 : ℝ) ≤
            (3763141294622501244829 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8501925424845501 / 10000000000000000 : ℝ) ≤
      Real.sqrt (23130475497483 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23130475497483 / 32000000000000 : ℝ) ≤ (132842584763211 / 156250000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23130475497483 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1014 :
    Real.arctan (1062740678105688 / 2890706478594065 : ℝ) ≤
      (220189323267150120757 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1013 :
    Real.arctan (132842584763211 / 156250000000000 : ℝ) ≤
      (2 * (220189323267150120757 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (328141295718813 / 250000000000000 : ℝ) ≤
          Real.sqrt (1 + (132842584763211 / 156250000000000 : ℝ) ^ 2))
      (by
        rw [show
            (132842584763211 / 156250000000000 : ℝ) /
                (1 + (328141295718813 / 250000000000000 : ℝ)) =
              (1062740678105688 / 2890706478594065 : ℝ)
            by
        norm_num];
        exact hau1014)
  have hat1 :
    (Real.pi / 2 - (2 * (220189323267150120757 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (156250000000000 / 132842584763211 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (156250000000000 / 132842584763211 : ℝ) =
              (132842584763211 / 156250000000000 : ℝ)
            by
        norm_num];
        exact hau1013)
  have hz1 :
    (156250000000000 / 132842584763211 : ℝ) ≤
      1 / Real.sqrt (23130475497483 / 32000000000000 : ℝ) := by
    rw [show (156250000000000 / 132842584763211 : ℝ) = 1 / (132842584763211 / 156250000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2833975141615167 : ℝ) ≤
      (439937726411396261549 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23130475497483 / 32000000000000 : ℝ) ≤
      (250000000000000 / 2833975141615167 : ℝ) := by
    rw [show
        (250000000000000 / 2833975141615167 : ℝ) =
          (3 / 40) / (8501925424845501 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (220189323267150120757 / 625000000000000000000 : ℝ))) -
        6 * (439937726411396261549 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23130475497483 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23130475497483 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8501925424845501 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (220189323267150120757 / 625000000000000000000 : ℝ))) -
          6 * (439937726411396261549 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (23130475497483 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23130475497483 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23130475497483 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_622 :
    ((5445194127762287189187 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(126210591564468617503 / 400000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1063440581285023 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3524653733925453359381 / 10000000000000000000000 : ℝ))) -
              6 * (219824836060368561831 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (579023805401 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (579023805401 / 800000000000 : ℝ)) =
      Real.log (1379023805401 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((579023805401 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (583523805401 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5445194127762287189187 / 10000000000000000000000 : ℝ) ≤
      Real.log (1379023805401 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (583523805401 / 800000000000 : ℝ) ≤
      (-(126210591564468617503 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (583523805401 / 800000000000 : ℝ) = (583523805401 / 400000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (583523805401 / 400000000000 : ℝ) ≤
            (151048280555531382497 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1063440581285023 / 1250000000000000 : ℝ) ≤ Real.sqrt (579023805401 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (579023805401 / 800000000000 : ℝ) ≤ (8507524650280187 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (579023805401 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau1016 :
    Real.arctan (8507524650280187 / 23129279328094325 : ℝ) ≤
      (3524653733925453359381 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1015 :
    Real.arctan (8507524650280187 / 10000000000000000 : ℝ) ≤
      (2 * (3524653733925453359381 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (525171173123773 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (8507524650280187 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8507524650280187 / 10000000000000000 : ℝ) /
                (1 + (525171173123773 / 400000000000000 : ℝ)) =
              (8507524650280187 / 23129279328094325 : ℝ)
            by
        norm_num];
        exact hau1016)
  have hat1 :
    (Real.pi / 2 - (2 * (3524653733925453359381 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8507524650280187 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8507524650280187 : ℝ) =
              (8507524650280187 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1015)
  have hz1 :
    (10000000000000000 / 8507524650280187 : ℝ) ≤
      1 / Real.sqrt (579023805401 / 800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8507524650280187 : ℝ) =
          1 / (8507524650280187 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 1063440581285023 : ℝ) ≤
      (219824836060368561831 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (579023805401 / 800000000000 : ℝ) ≤
      (93750000000000 / 1063440581285023 : ℝ) := by
    rw [show
        (93750000000000 / 1063440581285023 : ℝ) =
          (3 / 40) / (1063440581285023 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3524653733925453359381 / 10000000000000000000000 : ℝ))) -
        6 * (219824836060368561831 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (579023805401 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (579023805401 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1063440581285023 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3524653733925453359381 / 10000000000000000000000 : ℝ))) -
          6 * (219824836060368561831 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (579023805401 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (579023805401 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (579023805401 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_623 :
    ((85167463359885447783 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(314221611887456540269 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8513120193008883 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3526276330333639916337 / 10000000000000000000000 : ℝ))) -
              6 * (87872436582745622019 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (23191428934597 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23191428934597 / 32000000000000 : ℝ)) =
      Real.log (55191428934597 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23191428934597 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23371428934597 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (85167463359885447783 / 156250000000000000000 : ℝ) ≤
      Real.log (55191428934597 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23371428934597 / 32000000000000 : ℝ) ≤
      (-(314221611887456540269 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23371428934597 / 32000000000000 : ℝ) = (23371428934597 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23371428934597 / 16000000000000 : ℝ) ≤
            (378925568412543459731 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8513120193008883 / 10000000000000000 : ℝ) ≤
      Real.sqrt (23191428934597 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23191428934597 / 32000000000000 : ℝ) ≤ (4256560096504443 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23191428934597 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1018 :
    Real.arctan (8513120193008886 / 23132905825468163 : ℝ) ≤
      (3526276330333639916337 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1017 :
    Real.arctan (4256560096504443 / 5000000000000000 : ℝ) ≤
      (2 * (3526276330333639916337 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13132905825468163 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4256560096504443 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4256560096504443 / 5000000000000000 : ℝ) /
                (1 + (13132905825468163 / 10000000000000000 : ℝ)) =
              (8513120193008886 / 23132905825468163 : ℝ)
            by
        norm_num];
        exact hau1018)
  have hat1 :
    (Real.pi / 2 - (2 * (3526276330333639916337 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4256560096504443 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4256560096504443 : ℝ) =
              (4256560096504443 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1017)
  have hz1 :
    (5000000000000000 / 4256560096504443 : ℝ) ≤
      1 / Real.sqrt (23191428934597 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4256560096504443 : ℝ) = 1 / (4256560096504443 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2837706731002961 : ℝ) ≤
      (87872436582745622019 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23191428934597 / 32000000000000 : ℝ) ≤
      (250000000000000 / 2837706731002961 : ℝ) := by
    rw [show
        (250000000000000 / 2837706731002961 : ℝ) =
          (3 / 40) / (8513120193008883 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3526276330333639916337 / 10000000000000000000000 : ℝ))) -
        6 * (87872436582745622019 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23191428934597 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23191428934597 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8513120193008883 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3526276330333639916337 / 10000000000000000000000 : ℝ))) -
          6 * (87872436582745622019 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (23191428934597 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23191428934597 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23191428934597 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_624 :
    ((5456238133051884174373 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1564592226615293954067 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8518712060288587 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1763948482885999733877 / 5000000000000000000000 : ℝ))) -
              6 * (878150513890413655597 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11610952826577 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11610952826577 / 16000000000000 : ℝ)) =
      Real.log (27610952826577 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11610952826577 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11700952826577 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5456238133051884174373 / 10000000000000000000000 : ℝ) ≤
      Real.log (27610952826577 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11700952826577 / 16000000000000 : ℝ) ≤
      (-(1564592226615293954067 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11700952826577 / 16000000000000 : ℝ) = (11700952826577 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11700952826577 / 8000000000000 : ℝ) ≤
            (1901143674884706045933 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8518712060288587 / 10000000000000000 : ℝ) ≤
      Real.sqrt (11610952826577 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11610952826577 / 16000000000000 : ℝ) ≤ (851871206028859 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11610952826577 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1020 :
    Real.arctan (8518712060288590 / 23136531321703847 : ℝ) ≤
      (1763948482885999733877 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1019 :
    Real.arctan (851871206028859 / 1000000000000000 : ℝ) ≤
      (2 * (1763948482885999733877 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13136531321703847 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (851871206028859 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (851871206028859 / 1000000000000000 : ℝ) /
                (1 + (13136531321703847 / 10000000000000000 : ℝ)) =
              (8518712060288590 / 23136531321703847 : ℝ)
            by
        norm_num];
        exact hau1020)
  have hat1 :
    (Real.pi / 2 - (2 * (1763948482885999733877 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 851871206028859 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 851871206028859 : ℝ) =
              (851871206028859 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau1019)
  have hz1 :
    (1000000000000000 / 851871206028859 : ℝ) ≤
      1 / Real.sqrt (11610952826577 / 16000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 851871206028859 : ℝ) = 1 / (851871206028859 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8518712060288587 : ℝ) ≤
      (878150513890413655597 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11610952826577 / 16000000000000 : ℝ) ≤
      (750000000000000 / 8518712060288587 : ℝ) := by
    rw [show
        (750000000000000 / 8518712060288587 : ℝ) =
          (3 / 40) / (8518712060288587 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1763948482885999733877 / 5000000000000000000000 : ℝ))) -
        6 * (878150513890413655597 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11610952826577 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11610952826577 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8518712060288587 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1763948482885999733877 / 5000000000000000000000 : ℝ))) -
          6 * (878150513890413655597 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (11610952826577 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11610952826577 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11610952826577 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
