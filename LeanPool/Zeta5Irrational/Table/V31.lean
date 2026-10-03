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

/-! # V31: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_373 :
    ((3167046557416502155937 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9722736274507547290279 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3052036710852029 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2740184174711295780057 / 10000000000000000000000 : ℝ))) -
              6 * (1222560062854347182191 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (47692431792069 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47692431792069 / 128000000000000 : ℝ)) =
      Real.log (175692431792069 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47692431792069 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (48412431792069 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3167046557416502155937 / 10000000000000000000000 : ℝ) ≤
      Real.log (175692431792069 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (48412431792069 / 128000000000000 : ℝ) ≤
      (-(9722736274507547290279 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (48412431792069 / 128000000000000 : ℝ) = (48412431792069 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48412431792069 / 32000000000000 : ℝ) ≤
            (4140207331492452709721 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3052036710852029 / 5000000000000000 : ℝ) ≤
      Real.sqrt (47692431792069 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47692431792069 / 128000000000000 : ℝ) ≤
      (6104073421704061 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47692431792069 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau518 :
    Real.arctan (164974957343353 / 586913216729537 : ℝ) ≤
      (2740184174711295780057 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau517 :
    Real.arctan (6104073421704061 / 10000000000000000 : ℝ) ≤
      (2 * (2740184174711295780057 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11715789018992869 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6104073421704061 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6104073421704061 / 10000000000000000 : ℝ) /
                (1 + (11715789018992869 / 10000000000000000 : ℝ)) =
              (164974957343353 / 586913216729537 : ℝ)
            by
        norm_num];
        exact hau518)
  have hat1 :
    (Real.pi / 2 - (2 * (2740184174711295780057 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6104073421704061 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6104073421704061 : ℝ) =
              (6104073421704061 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau517)
  have hz1 :
    (10000000000000000 / 6104073421704061 : ℝ) ≤
      1 / Real.sqrt (47692431792069 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6104073421704061 : ℝ) =
          1 / (6104073421704061 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3052036710852029 : ℝ) ≤
      (1222560062854347182191 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47692431792069 / 128000000000000 : ℝ) ≤
      (375000000000000 / 3052036710852029 : ℝ) := by
    rw [show
        (375000000000000 / 3052036710852029 : ℝ) =
          (3 / 40) / (3052036710852029 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2740184174711295780057 / 10000000000000000000000 : ℝ))) -
        6 * (1222560062854347182191 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47692431792069 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47692431792069 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3052036710852029 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2740184174711295780057 / 10000000000000000000000 : ℝ))) -
          6 * (1222560062854347182191 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (47692431792069 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47692431792069 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47692431792069 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_374 :
    ((3171810405818957948811 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4852729359299315616467 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((305471424036659 / 500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2742134413310491105127 / 10000000000000000000000 : ℝ))) -
              6 * (610749546040129944137 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (5972018617791 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5972018617791 / 16000000000000 : ℝ)) =
      Real.log (21972018617791 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5972018617791 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6062018617791 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3171810405818957948811 / 10000000000000000000000 : ℝ) ≤
      Real.log (21972018617791 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6062018617791 / 16000000000000 : ℝ) ≤
      (-(4852729359299315616467 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (6062018617791 / 16000000000000 : ℝ) = (6062018617791 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6062018617791 / 4000000000000 : ℝ) ≤
            (2078742443700684383533 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (305471424036659 / 500000000000000 : ℝ) ≤ Real.sqrt (5972018617791 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5972018617791 / 16000000000000 : ℝ) ≤ (6109428480733183 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5972018617791 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau520 :
    Real.arctan (6109428480733183 / 21718579963510670 : ℝ) ≤
      (2742134413310491105127 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau519 :
    Real.arctan (6109428480733183 / 10000000000000000 : ℝ) ≤
      (2 * (2742134413310491105127 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1171857996351067 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6109428480733183 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6109428480733183 / 10000000000000000 : ℝ) /
                (1 + (1171857996351067 / 1000000000000000 : ℝ)) =
              (6109428480733183 / 21718579963510670 : ℝ)
            by
        norm_num];
        exact hau520)
  have hat1 :
    (Real.pi / 2 - (2 * (2742134413310491105127 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6109428480733183 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6109428480733183 : ℝ) =
              (6109428480733183 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau519)
  have hz1 :
    (10000000000000000 / 6109428480733183 : ℝ) ≤
      1 / Real.sqrt (5972018617791 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6109428480733183 : ℝ) =
          1 / (6109428480733183 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (37500000000000 / 305471424036659 : ℝ) ≤
      (610749546040129944137 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5972018617791 / 16000000000000 : ℝ) ≤
      (37500000000000 / 305471424036659 : ℝ) := by
    rw [show
        (37500000000000 / 305471424036659 : ℝ) =
          (3 / 40) / (305471424036659 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2742134413310491105127 / 10000000000000000000000 : ℝ))) -
        6 * (610749546040129944137 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5972018617791 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5972018617791 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((305471424036659 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2742134413310491105127 / 10000000000000000000000 : ℝ))) -
          6 * (610749546040129944137 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (5972018617791 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5972018617791 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5972018617791 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_375 :
    ((1588285992938407841959 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9688210962603965581069 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3057389425017427 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1372041008083511690423 / 5000000000000000000000 : ℝ))) -
              6 * (305110219698251537417 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (47859866092587 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47859866092587 / 128000000000000 : ℝ)) =
      Real.log (175859866092587 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47859866092587 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (48579866092587 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1588285992938407841959 / 5000000000000000000000 : ℝ) ≤
      Real.log (175859866092587 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (48579866092587 / 128000000000000 : ℝ) ≤
      (-(9688210962603965581069 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (48579866092587 / 128000000000000 : ℝ) = (48579866092587 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48579866092587 / 32000000000000 : ℝ) ≤
            (4174732643396034418931 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3057389425017427 / 5000000000000000 : ℝ) ≤
      Real.sqrt (47859866092587 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47859866092587 / 128000000000000 : ℝ) ≤
      (6114778850034857 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47859866092587 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau522 :
    Real.arctan (6114778850034857 / 21721370243484060 : ℝ) ≤
      (1372041008083511690423 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau521 :
    Real.arctan (6114778850034857 / 10000000000000000 : ℝ) ≤
      (2 * (1372041008083511690423 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (586068512174203 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (6114778850034857 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6114778850034857 / 10000000000000000 : ℝ) /
                (1 + (586068512174203 / 500000000000000 : ℝ)) =
              (6114778850034857 / 21721370243484060 : ℝ)
            by
        norm_num];
        exact hau522)
  have hat1 :
    (Real.pi / 2 - (2 * (1372041008083511690423 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6114778850034857 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6114778850034857 : ℝ) =
              (6114778850034857 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau521)
  have hz1 :
    (10000000000000000 / 6114778850034857 : ℝ) ≤
      1 / Real.sqrt (47859866092587 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6114778850034857 : ℝ) =
          1 / (6114778850034857 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3057389425017427 : ℝ) ≤
      (305110219698251537417 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47859866092587 / 128000000000000 : ℝ) ≤
      (375000000000000 / 3057389425017427 : ℝ) := by
    rw [show
        (375000000000000 / 3057389425017427 : ℝ) =
          (3 / 40) / (3057389425017427 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1372041008083511690423 / 5000000000000000000000 : ℝ))) -
        6 * (305110219698251537417 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47859866092587 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47859866092587 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3057389425017427 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1372041008083511690423 / 5000000000000000000000 : ℝ))) -
          6 * (305110219698251537417 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (47859866092587 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47859866092587 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47859866092587 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_376 :
    ((3181331299749228225409 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4835496451952082468179 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((76501556773859 / 125000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (686506747566213541199 / 2500000000000000000000 : ℝ))) -
              6 * (243877082213678186227 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (23971791621423 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23971791621423 / 64000000000000 : ℝ)) =
      Real.log (87971791621423 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23971791621423 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (24331791621423 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3181331299749228225409 / 10000000000000000000000 : ℝ) ≤
      Real.log (87971791621423 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (24331791621423 / 64000000000000 : ℝ) ≤
      (-(4835496451952082468179 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (24331791621423 / 64000000000000 : ℝ) = (24331791621423 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24331791621423 / 16000000000000 : ℝ) ≤
            (2095975351047917531821 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (76501556773859 / 125000000000000 : ℝ) ≤ Real.sqrt (23971791621423 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23971791621423 / 64000000000000 : ℝ) ≤
      (6120124541908723 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23971791621423 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau524 :
    Real.arctan (6120124541908723 / 21724159859387513 : ℝ) ≤
      (686506747566213541199 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau523 :
    Real.arctan (6120124541908723 / 10000000000000000 : ℝ) ≤
      (2 * (686506747566213541199 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11724159859387513 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6120124541908723 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6120124541908723 / 10000000000000000 : ℝ) /
                (1 + (11724159859387513 / 10000000000000000 : ℝ)) =
              (6120124541908723 / 21724159859387513 : ℝ)
            by
        norm_num];
        exact hau524)
  have hat1 :
    (Real.pi / 2 - (2 * (686506747566213541199 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6120124541908723 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6120124541908723 : ℝ) =
              (6120124541908723 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau523)
  have hz1 :
    (10000000000000000 / 6120124541908723 : ℝ) ≤
      1 / Real.sqrt (23971791621423 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6120124541908723 : ℝ) =
          1 / (6120124541908723 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (9375000000000 / 76501556773859 : ℝ) ≤
      (243877082213678186227 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23971791621423 / 64000000000000 : ℝ) ≤
      (9375000000000 / 76501556773859 : ℝ) := by
    rw [show
        (9375000000000 / 76501556773859 : ℝ) = (3 / 40) / (76501556773859 / 125000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (686506747566213541199 / 2500000000000000000000 : ℝ))) -
        6 * (243877082213678186227 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23971791621423 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23971791621423 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((76501556773859 / 125000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (686506747566213541199 / 2500000000000000000000 : ℝ))) -
          6 * (243877082213678186227 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (23971791621423 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23971791621423 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23971791621423 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_377 :
    ((19913052184951669237 / 62500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4826902220204502580303 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3062732784300373 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (171748083909903721723 / 625000000000000000000 : ℝ))) -
              6 * (15229158463178572059 / 125000000000000000000 : ℝ)))) ≤
      Vfield (9605460078621 / 25600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9605460078621 / 25600000000000 : ℝ)) =
      Real.log (35205460078621 / 25600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9605460078621 / 25600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9749460078621 / 25600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (19913052184951669237 / 62500000000000000000 : ℝ) ≤
      Real.log (35205460078621 / 25600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9749460078621 / 25600000000000 : ℝ) ≤
      (-(4826902220204502580303 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9749460078621 / 25600000000000 : ℝ) = (9749460078621 / 6400000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9749460078621 / 6400000000000 : ℝ) ≤
            (2104569582795497419697 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3062732784300373 / 5000000000000000 : ℝ) ≤ Real.sqrt (9605460078621 / 25600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9605460078621 / 25600000000000 : ℝ) ≤ (6125465568600749 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9605460078621 / 25600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau526 :
    Real.arctan (6125465568600749 / 21726948811694936 : ℝ) ≤
      (171748083909903721723 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau525 :
    Real.arctan (6125465568600749 / 10000000000000000 : ℝ) ≤
      (2 * (171748083909903721723 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1465868601461867 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (6125465568600749 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6125465568600749 / 10000000000000000 : ℝ) /
                (1 + (1465868601461867 / 1250000000000000 : ℝ)) =
              (6125465568600749 / 21726948811694936 : ℝ)
            by
        norm_num];
        exact hau526)
  have hat1 :
    (Real.pi / 2 - (2 * (171748083909903721723 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6125465568600749 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6125465568600749 : ℝ) =
              (6125465568600749 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau525)
  have hz1 :
    (10000000000000000 / 6125465568600749 : ℝ) ≤
      1 / Real.sqrt (9605460078621 / 25600000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6125465568600749 : ℝ) =
          1 / (6125465568600749 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3062732784300373 : ℝ) ≤
      (15229158463178572059 / 125000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9605460078621 / 25600000000000 : ℝ) ≤
      (375000000000000 / 3062732784300373 : ℝ) := by
    rw [show
        (375000000000000 / 3062732784300373 : ℝ) =
          (3 / 40) / (3062732784300373 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (171748083909903721723 / 625000000000000000000 : ℝ))) -
        6 * (15229158463178572059 / 125000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9605460078621 / 25600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9605460078621 / 25600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3062732784300373 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (171748083909903721723 / 625000000000000000000 : ℝ))) -
          6 * (15229158463178572059 / 125000000000000000000 : ℝ))) ≤
      Real.sqrt (9605460078621 / 25600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9605460078621 / 25600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9605460078621 / 25600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_378 :
    ((1595421568779464123529 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9636645470553791427333 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((153270048557589 / 250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (54998181599460134389 / 200000000000000000000 : ℝ))) -
              6 * (608641332485034393921 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (12027754385841 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (12027754385841 / 32000000000000 : ℝ)) =
      Real.log (44027754385841 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((12027754385841 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (12207754385841 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1595421568779464123529 / 5000000000000000000000 : ℝ) ≤
      Real.log (44027754385841 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (12207754385841 / 32000000000000 : ℝ) ≤
      (-(9636645470553791427333 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (12207754385841 / 32000000000000 : ℝ) = (12207754385841 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12207754385841 / 8000000000000 : ℝ) ≤
            (4226298135446208572667 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (153270048557589 / 250000000000000 : ℝ) ≤ Real.sqrt (12027754385841 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (12027754385841 / 32000000000000 : ℝ) ≤
      (6130801942303563 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (12027754385841 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau528 :
    Real.arctan (6130801942303563 / 21729737100879674 : ℝ) ≤
      (54998181599460134389 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau527 :
    Real.arctan (6130801942303563 / 10000000000000000 : ℝ) ≤
      (2 * (54998181599460134389 / 200000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5864868550439837 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6130801942303563 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6130801942303563 / 10000000000000000 : ℝ) /
                (1 + (5864868550439837 / 5000000000000000 : ℝ)) =
              (6130801942303563 / 21729737100879674 : ℝ)
            by
        norm_num];
        exact hau528)
  have hat1 :
    (Real.pi / 2 - (2 * (54998181599460134389 / 200000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6130801942303563 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6130801942303563 : ℝ) =
              (6130801942303563 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau527)
  have hz1 :
    (10000000000000000 / 6130801942303563 : ℝ) ≤
      1 / Real.sqrt (12027754385841 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6130801942303563 : ℝ) =
          1 / (6130801942303563 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (6250000000000 / 51090016185863 : ℝ) ≤
      (608641332485034393921 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (12027754385841 / 32000000000000 : ℝ) ≤
      (6250000000000 / 51090016185863 : ℝ) := by
    rw [show
        (6250000000000 / 51090016185863 : ℝ) = (3 / 40) / (153270048557589 / 250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (54998181599460134389 / 200000000000000000000 : ℝ))) -
        6 * (608641332485034393921 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (12027754385841 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (12027754385841 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((153270048557589 / 250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (54998181599460134389 / 200000000000000000000 : ℝ))) -
          6 * (608641332485034393921 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (12027754385841 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (12027754385841 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (12027754385841 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_379 :
    ((798898916449784521491 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9619515893295757380253 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1534033418789193 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2751846209404526497207 / 10000000000000000000000 : ℝ))) -
              6 * (1216235363106071541963 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (48194734693623 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (48194734693623 / 128000000000000 : ℝ)) =
      Real.log (176194734693623 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((48194734693623 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (48914734693623 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (798898916449784521491 / 2500000000000000000000 : ℝ) ≤
      Real.log (176194734693623 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (48914734693623 / 128000000000000 : ℝ) ≤
      (-(9619515893295757380253 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (48914734693623 / 128000000000000 : ℝ) = (48914734693623 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48914734693623 / 32000000000000 : ℝ) ≤
            (4243427712704242619747 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1534033418789193 / 2500000000000000 : ℝ) ≤
      Real.sqrt (48194734693623 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (48194734693623 / 128000000000000 : ℝ) ≤ (245445347006271 / 400000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (48194734693623 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau530 :
    Real.arctan (6136133675156775 / 21732524727414511 : ℝ) ≤
      (2751846209404526497207 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau529 :
    Real.arctan (245445347006271 / 400000000000000 : ℝ) ≤
      (2 * (2751846209404526497207 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11732524727414511 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (245445347006271 / 400000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (245445347006271 / 400000000000000 : ℝ) /
                (1 + (11732524727414511 / 10000000000000000 : ℝ)) =
              (6136133675156775 / 21732524727414511 : ℝ)
            by
        norm_num];
        exact hau530)
  have hat1 :
    (Real.pi / 2 - (2 * (2751846209404526497207 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (400000000000000 / 245445347006271 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 245445347006271 : ℝ) =
              (245445347006271 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau529)
  have hz1 :
    (400000000000000 / 245445347006271 : ℝ) ≤
      1 / Real.sqrt (48194734693623 / 128000000000000 : ℝ) := by
    rw [show (400000000000000 / 245445347006271 : ℝ) = 1 / (245445347006271 / 400000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 511344472929731 : ℝ) ≤
      (1216235363106071541963 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (48194734693623 / 128000000000000 : ℝ) ≤
      (62500000000000 / 511344472929731 : ℝ) := by
    rw [show
        (62500000000000 / 511344472929731 : ℝ) =
          (3 / 40) / (1534033418789193 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2751846209404526497207 / 10000000000000000000000 : ℝ))) -
        6 * (1216235363106071541963 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (48194734693623 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (48194734693623 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1534033418789193 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2751846209404526497207 / 10000000000000000000000 : ℝ))) -
          6 * (1216235363106071541963 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (48194734693623 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (48194734693623 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (48194734693623 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_380 :
    ((1600172968229879563989 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9602415608110495079503 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1228292155849459 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2753780737720085654817 / 10000000000000000000000 : ℝ))) -
              6 * (303797689955757674163 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (24139225921941 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (24139225921941 / 64000000000000 : ℝ)) =
      Real.log (88139225921941 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((24139225921941 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (24499225921941 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1600172968229879563989 / 5000000000000000000000 : ℝ) ≤
      Real.log (88139225921941 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (24499225921941 / 64000000000000 : ℝ) ≤
      (-(9602415608110495079503 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (24499225921941 / 64000000000000 : ℝ) = (24499225921941 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24499225921941 / 16000000000000 : ℝ) ≤
            (4260527997889504920497 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1228292155849459 / 2000000000000000 : ℝ) ≤ Real.sqrt (24139225921941 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (24139225921941 / 64000000000000 : ℝ) ≤ (3070730389623649 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (24139225921941 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau532 :
    Real.arctan (6141460779247298 / 21735311691771667 : ℝ) ≤
      (2753780737720085654817 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau531 :
    Real.arctan (3070730389623649 / 5000000000000000 : ℝ) ≤
      (2 * (2753780737720085654817 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11735311691771667 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3070730389623649 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3070730389623649 / 5000000000000000 : ℝ) /
                (1 + (11735311691771667 / 10000000000000000 : ℝ)) =
              (6141460779247298 / 21735311691771667 : ℝ)
            by
        norm_num];
        exact hau532)
  have hat1 :
    (Real.pi / 2 - (2 * (2753780737720085654817 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3070730389623649 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3070730389623649 : ℝ) =
              (3070730389623649 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau531)
  have hz1 :
    (5000000000000000 / 3070730389623649 : ℝ) ≤
      1 / Real.sqrt (24139225921941 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3070730389623649 : ℝ) = 1 / (3070730389623649 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1228292155849459 : ℝ) ≤
      (303797689955757674163 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (24139225921941 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1228292155849459 : ℝ) := by
    rw [show
        (150000000000000 / 1228292155849459 : ℝ) =
          (3 / 40) / (1228292155849459 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2753780737720085654817 / 10000000000000000000000 : ℝ))) -
        6 * (303797689955757674163 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (24139225921941 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (24139225921941 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1228292155849459 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2753780737720085654817 / 10000000000000000000000 : ℝ))) -
          6 * (303797689955757674163 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (24139225921941 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (24139225921941 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (24139225921941 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_381 :
    ((1602546975842297952737 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9585344514988415420279 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6146783266609669 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (275571267175795931953 / 1000000000000000000000 : ℝ))) -
              6 * (75884302721971491671 / 625000000000000000000 : ℝ)))) ≤
      Vfield (48362168994141 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (48362168994141 / 128000000000000 : ℝ)) =
      Real.log (176362168994141 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((48362168994141 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (49082168994141 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1602546975842297952737 / 5000000000000000000000 : ℝ) ≤
      Real.log (176362168994141 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (49082168994141 / 128000000000000 : ℝ) ≤
      (-(9585344514988415420279 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (49082168994141 / 128000000000000 : ℝ) = (49082168994141 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49082168994141 / 32000000000000 : ℝ) ≤
            (4277599091011584579721 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6146783266609669 / 10000000000000000 : ℝ) ≤
      Real.sqrt (48362168994141 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (48362168994141 / 128000000000000 : ℝ) ≤ (768347908326209 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (48362168994141 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau534 :
    Real.arctan (6146783266609672 / 21738097994422803 : ℝ) ≤
      (275571267175795931953 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau533 :
    Real.arctan (768347908326209 / 1250000000000000 : ℝ) ≤
      (2 * (275571267175795931953 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11738097994422803 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (768347908326209 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (768347908326209 / 1250000000000000 : ℝ) /
                (1 + (11738097994422803 / 10000000000000000 : ℝ)) =
              (6146783266609672 / 21738097994422803 : ℝ)
            by
        norm_num];
        exact hau534)
  have hat1 :
    (Real.pi / 2 - (2 * (275571267175795931953 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 768347908326209 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 768347908326209 : ℝ) =
              (768347908326209 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau533)
  have hz1 :
    (1250000000000000 / 768347908326209 : ℝ) ≤
      1 / Real.sqrt (48362168994141 / 128000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 768347908326209 : ℝ) = 1 / (768347908326209 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6146783266609669 : ℝ) ≤
      (75884302721971491671 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (48362168994141 / 128000000000000 : ℝ) ≤
      (750000000000000 / 6146783266609669 : ℝ) := by
    rw [show
        (750000000000000 / 6146783266609669 : ℝ) =
          (3 / 40) / (6146783266609669 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (275571267175795931953 / 1000000000000000000000 : ℝ))) -
        6 * (75884302721971491671 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (48362168994141 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (48362168994141 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6146783266609669 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (275571267175795931953 / 1000000000000000000000 : ℝ))) -
          6 * (75884302721971491671 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (48362168994141 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (48362168994141 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (48362168994141 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_382 :
    ((320983971361440075487 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1196037814303904839033 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((49216809193811 / 80000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (551528403665559915819 / 2000000000000000000000 : ℝ))) -
              6 * (1213109602791532020873 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (121114715361 / 320000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (121114715361 / 320000000000 : ℝ)) =
      Real.log (441114715361 / 320000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((121114715361 / 320000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (122914715361 / 320000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (320983971361440075487 / 1000000000000000000000 : ℝ) ≤
      Real.log (441114715361 / 320000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (122914715361 / 320000000000 : ℝ) ≤
      (-(1196037814303904839033 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (122914715361 / 320000000000 : ℝ) = (122914715361 / 80000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (122914715361 / 80000000000 : ℝ) ≤
            (536830136446095160967 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (49216809193811 / 80000000000000 : ℝ) ≤ Real.sqrt (121114715361 / 320000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (121114715361 / 320000000000 : ℝ) ≤ (3076050574613189 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (121114715361 / 320000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau536 :
    Real.arctan (3076050574613189 / 10870441817919510 : ℝ) ≤
      (551528403665559915819 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau535 :
    Real.arctan (3076050574613189 / 5000000000000000 : ℝ) ≤
      (2 * (551528403665559915819 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (587044181791951 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3076050574613189 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3076050574613189 / 5000000000000000 : ℝ) /
                (1 + (587044181791951 / 500000000000000 : ℝ)) =
              (3076050574613189 / 10870441817919510 : ℝ)
            by
        norm_num];
        exact hau536)
  have hat1 :
    (Real.pi / 2 - (2 * (551528403665559915819 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3076050574613189 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3076050574613189 : ℝ) =
              (3076050574613189 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau535)
  have hz1 :
    (5000000000000000 / 3076050574613189 : ℝ) ≤ 1 / Real.sqrt (121114715361 / 320000000000 : ℝ) :=
  by
    rw [show
        (5000000000000000 / 3076050574613189 : ℝ) = 1 / (3076050574613189 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (6000000000000 / 49216809193811 : ℝ) ≤
      (1213109602791532020873 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (121114715361 / 320000000000 : ℝ) ≤
      (6000000000000 / 49216809193811 : ℝ) := by
    rw [show
        (6000000000000 / 49216809193811 : ℝ) = (3 / 40) / (49216809193811 / 80000000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (551528403665559915819 / 2000000000000000000000 : ℝ))) -
        6 * (1213109602791532020873 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (121114715361 / 320000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (121114715361 / 320000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((49216809193811 / 80000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (551528403665559915819 / 2000000000000000000000 : ℝ))) -
          6 * (1213109602791532020873 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (121114715361 / 320000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (121114715361 / 320000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (121114715361 / 320000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_383 :
    ((3214583224386879607881 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1193911188431064389001 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1539353609757037 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (86236524506587603067 / 312500000000000000000 : ℝ))) -
              6 * (60603651305585332871 / 500000000000000000000 : ℝ)))) ≤
      Vfield (48529603294659 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (48529603294659 / 128000000000000 : ℝ)) =
      Real.log (176529603294659 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((48529603294659 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (49249603294659 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3214583224386879607881 / 10000000000000000000000 : ℝ) ≤
      Real.log (176529603294659 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (49249603294659 / 128000000000000 : ℝ) ≤
      (-(1193911188431064389001 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (49249603294659 / 128000000000000 : ℝ) = (49249603294659 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49249603294659 / 32000000000000 : ℝ) ≤
            (538956762318935610999 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1539353609757037 / 2500000000000000 : ℝ) ≤
      Real.sqrt (48529603294659 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (48529603294659 / 128000000000000 : ℝ) ≤
      (6157414439028151 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (48529603294659 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau538 :
    Real.arctan (6157414439028151 / 21743668616490859 : ℝ) ≤
      (86236524506587603067 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau537 :
    Real.arctan (6157414439028151 / 10000000000000000 : ℝ) ≤
      (2 * (86236524506587603067 / 312500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11743668616490859 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6157414439028151 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6157414439028151 / 10000000000000000 : ℝ) /
                (1 + (11743668616490859 / 10000000000000000 : ℝ)) =
              (6157414439028151 / 21743668616490859 : ℝ)
            by
        norm_num];
        exact hau538)
  have hat1 :
    (Real.pi / 2 - (2 * (86236524506587603067 / 312500000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6157414439028151 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6157414439028151 : ℝ) =
              (6157414439028151 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau537)
  have hz1 :
    (10000000000000000 / 6157414439028151 : ℝ) ≤
      1 / Real.sqrt (48529603294659 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6157414439028151 : ℝ) =
          1 / (6157414439028151 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1539353609757037 : ℝ) ≤
      (60603651305585332871 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (48529603294659 / 128000000000000 : ℝ) ≤
      (187500000000000 / 1539353609757037 : ℝ) := by
    rw [show
        (187500000000000 / 1539353609757037 : ℝ) =
          (3 / 40) / (1539353609757037 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (86236524506587603067 / 312500000000000000000 : ℝ))) -
        6 * (60603651305585332871 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (48529603294659 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (48529603294659 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1539353609757037 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (86236524506587603067 / 312500000000000000000 : ℝ))) -
          6 * (60603651305585332871 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (48529603294659 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (48529603294659 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (48529603294659 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_384 :
    ((643864897227339553809 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9534305395554174604017 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1232544629578859 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (276149297615988133653 / 1000000000000000000000 : ℝ))) -
              6 * (242207820429808106391 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (24306660222459 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (24306660222459 / 64000000000000 : ℝ)) =
      Real.log (88306660222459 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((24306660222459 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (24666660222459 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (643864897227339553809 / 2000000000000000000000 : ℝ) ≤
      Real.log (88306660222459 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (24666660222459 / 64000000000000 : ℝ) ≤
      (-(9534305395554174604017 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (24666660222459 / 64000000000000 : ℝ) = (24666660222459 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24666660222459 / 16000000000000 : ℝ) ≤
            (4328638210445825395983 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1232544629578859 / 2000000000000000 : ℝ) ≤ Real.sqrt (24306660222459 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (24306660222459 / 64000000000000 : ℝ) ≤ (3081361573947149 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (24306660222459 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau540 :
    Real.arctan (143319142974286 / 505731463647635 : ℝ) ≤
      (276149297615988133653 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau539 :
    Real.arctan (3081361573947149 / 5000000000000000 : ℝ) ≤
      (2 * (276149297615988133653 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2349290587369661 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3081361573947149 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3081361573947149 / 5000000000000000 : ℝ) /
                (1 + (2349290587369661 / 2000000000000000 : ℝ)) =
              (143319142974286 / 505731463647635 : ℝ)
            by
        norm_num];
        exact hau540)
  have hat1 :
    (Real.pi / 2 - (2 * (276149297615988133653 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3081361573947149 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3081361573947149 : ℝ) =
              (3081361573947149 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau539)
  have hz1 :
    (5000000000000000 / 3081361573947149 : ℝ) ≤
      1 / Real.sqrt (24306660222459 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3081361573947149 : ℝ) = 1 / (3081361573947149 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1232544629578859 : ℝ) ≤
      (242207820429808106391 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (24306660222459 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1232544629578859 : ℝ) := by
    rw [show
        (150000000000000 / 1232544629578859 : ℝ) =
          (3 / 40) / (1232544629578859 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (276149297615988133653 / 1000000000000000000000 : ℝ))) -
        6 * (242207820429808106391 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (24306660222459 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (24306660222459 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1232544629578859 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (276149297615988133653 / 1000000000000000000000 : ℝ))) -
          6 * (242207820429808106391 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (24306660222459 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (24306660222459 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (24306660222459 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
