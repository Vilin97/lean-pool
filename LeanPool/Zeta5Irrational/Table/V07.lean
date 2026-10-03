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

/-! # V07: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_85 :
    ((226771874510981741379 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14780287962918279265411 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((430806739120629 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1060808378329828977447 / 5000000000000000000000 : ℝ)) -
              6 * (41882007321997290791 / 125000000000000000000 : ℝ)))) ≤
      Vfield (742377785887 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (742377785887 / 16000000000000 : ℝ)) =
      Real.log (16742377785887 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((742377785887 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (832377785887 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (226771874510981741379 / 5000000000000000000000 : ℝ) ≤
      Real.log (16742377785887 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (832377785887 / 16000000000000 : ℝ) ≤
      (-(14780287962918279265411 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (832377785887 / 16000000000000 : ℝ) = (832377785887 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (832377785887 / 500000000000 : ℝ) ≤
            (2548391544581720734589 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (430806739120629 / 2000000000000000 : ℝ) ≤ Real.sqrt (742377785887 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (742377785887 / 16000000000000 : ℝ) ≤ (538508423900787 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (742377785887 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau147 :
    Real.arctan (538508423900787 / 2500000000000000 : ℝ) ≤
      (1060808378329828977447 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1060808378329828977447 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 538508423900787 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 538508423900787 : ℝ) =
              (538508423900787 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau147)
  have hz1 :
    (2500000000000000 / 538508423900787 : ℝ) ≤
      1 / Real.sqrt (742377785887 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 538508423900787 : ℝ) = 1 / (538508423900787 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 143602246373543 : ℝ) ≤
      (41882007321997290791 / 125000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (742377785887 / 16000000000000 : ℝ) ≤
      (50000000000000 / 143602246373543 : ℝ) := by
    rw [show
        (50000000000000 / 143602246373543 : ℝ) =
          (3 / 40) / (430806739120629 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1060808378329828977447 / 5000000000000000000000 : ℝ)) -
        6 * (41882007321997290791 / 125000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (742377785887 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (742377785887 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((430806739120629 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1060808378329828977447 / 5000000000000000000000 : ℝ)) -
          6 * (41882007321997290791 / 125000000000000000000 : ℝ))) ≤
      Real.sqrt (742377785887 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (742377785887 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (742377785887 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_86 :
    ((457118096870510924543 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29488926237277907956139 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2162699649333341 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2129896972254185019601 / 10000000000000000000000 : ℝ)) -
              6 * (834527990154732413477 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (598690530973 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (598690530973 / 12800000000000 : ℝ)) =
      Real.log (13398690530973 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((598690530973 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (670690530973 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (457118096870510924543 / 10000000000000000000000 : ℝ) ≤
      Real.log (13398690530973 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (670690530973 / 12800000000000 : ℝ) ≤
      (-(29488926237277907956139 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (670690530973 / 12800000000000 : ℝ) = (670690530973 / 400000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (670690530973 / 400000000000 : ℝ) ≤
            (5168432777722092043861 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2162699649333341 / 10000000000000000 : ℝ) ≤ Real.sqrt (598690530973 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (598690530973 / 12800000000000 : ℝ) ≤ (67584364041667 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (598690530973 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau148 :
    Real.arctan (67584364041667 / 312500000000000 : ℝ) ≤
      (2129896972254185019601 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2129896972254185019601 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (312500000000000 / 67584364041667 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 67584364041667 : ℝ) =
              (67584364041667 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau148)
  have hz1 :
    (312500000000000 / 67584364041667 : ℝ) ≤ 1 / Real.sqrt (598690530973 / 12800000000000 : ℝ) := by
    rw [show (312500000000000 / 67584364041667 : ℝ) = 1 / (67584364041667 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2162699649333341 : ℝ) ≤
      (834527990154732413477 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (598690530973 / 12800000000000 : ℝ) ≤
      (750000000000000 / 2162699649333341 : ℝ) := by
    rw [show
        (750000000000000 / 2162699649333341 : ℝ) =
          (3 / 40) / (2162699649333341 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2129896972254185019601 / 10000000000000000000000 : ℝ)) -
        6 * (834527990154732413477 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (598690530973 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (598690530973 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2162699649333341 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2129896972254185019601 / 10000000000000000000000 : ℝ)) -
          6 * (834527990154732413477 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (598690530973 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (598690530973 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (598690530973 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_87 :
    ((460691167579284695889 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29417786266558953428469 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2171331016832617 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2138141194336938362321 / 10000000000000000000000 : ℝ)) -
              6 * (3325801225385149696601 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1508697083091 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1508697083091 / 32000000000000 : ℝ)) =
      Real.log (33508697083091 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1508697083091 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1688697083091 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (460691167579284695889 / 10000000000000000000000 : ℝ) ≤
      Real.log (33508697083091 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1688697083091 / 32000000000000 : ℝ) ≤
      (-(29417786266558953428469 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1688697083091 / 32000000000000 : ℝ) = (1688697083091 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1688697083091 / 1000000000000 : ℝ) ≤
            (5239572748441046571531 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2171331016832617 / 10000000000000000 : ℝ) ≤ Real.sqrt (1508697083091 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1508697083091 / 32000000000000 : ℝ) ≤ (108566550841631 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1508697083091 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau149 :
    Real.arctan (108566550841631 / 500000000000000 : ℝ) ≤
      (2138141194336938362321 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2138141194336938362321 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 108566550841631 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 108566550841631 : ℝ) =
              (108566550841631 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau149)
  have hz1 :
    (500000000000000 / 108566550841631 : ℝ) ≤
      1 / Real.sqrt (1508697083091 / 32000000000000 : ℝ) := by
    rw [show (500000000000000 / 108566550841631 : ℝ) = 1 / (108566550841631 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2171331016832617 : ℝ) ≤
      (3325801225385149696601 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1508697083091 / 32000000000000 : ℝ) ≤
      (750000000000000 / 2171331016832617 : ℝ) := by
    rw [show
        (750000000000000 / 2171331016832617 : ℝ) =
          (3 / 40) / (2171331016832617 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2138141194336938362321 / 10000000000000000000000 : ℝ)) -
        6 * (3325801225385149696601 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1508697083091 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1508697083091 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2171331016832617 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2138141194336938362321 / 10000000000000000000000 : ℝ)) -
          6 * (3325801225385149696601 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1508697083091 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1508697083091 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1508697083091 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_88 :
    ((464262962060620974379 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29347148812585080077493 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((435985641786157 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (429269968176594904411 / 2000000000000000000000 : ℝ)) -
              6 * (1656812925087286155121 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3041335677499 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3041335677499 / 64000000000000 : ℝ)) =
      Real.log (67041335677499 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3041335677499 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3401335677499 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (464262962060620974379 / 10000000000000000000000 : ℝ) ≤
      Real.log (67041335677499 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3401335677499 / 64000000000000 : ℝ) ≤
      (-(29347148812585080077493 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (3401335677499 / 64000000000000 : ℝ) = (3401335677499 / 2000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3401335677499 / 2000000000000 : ℝ) ≤
            (5310210202414919922507 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (435985641786157 / 2000000000000000 : ℝ) ≤ Real.sqrt (3041335677499 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3041335677499 / 64000000000000 : ℝ) ≤ (544982052232697 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3041335677499 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau150 :
    Real.arctan (544982052232697 / 2500000000000000 : ℝ) ≤
      (429269968176594904411 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (429269968176594904411 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 544982052232697 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 544982052232697 : ℝ) =
              (544982052232697 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau150)
  have hz1 :
    (2500000000000000 / 544982052232697 : ℝ) ≤
      1 / Real.sqrt (3041335677499 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 544982052232697 : ℝ) = 1 / (544982052232697 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 435985641786157 : ℝ) ≤
      (1656812925087286155121 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3041335677499 / 64000000000000 : ℝ) ≤
      (150000000000000 / 435985641786157 : ℝ) := by
    rw [show
        (150000000000000 / 435985641786157 : ℝ) =
          (3 / 40) / (435985641786157 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (429269968176594904411 / 2000000000000000000000 : ℝ)) -
        6 * (1656812925087286155121 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3041335677499 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3041335677499 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((435985641786157 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (429269968176594904411 / 2000000000000000000000 : ℝ)) -
          6 * (1656812925087286155121 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3041335677499 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3041335677499 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3041335677499 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_89 :
    ((233916740612939341691 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3659625853224161050433 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((437698325677629 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2154523321717564278481 / 10000000000000000000000 : ℝ)) -
              6 * (1320633347875011933 / 4000000000000000000 : ℝ)))) ≤
      Vfield (191579824301 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (191579824301 / 4000000000000 : ℝ)) =
      Real.log (4191579824301 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((191579824301 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (214079824301 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (233916740612939341691 / 5000000000000000000000 : ℝ) ≤
      Real.log (4191579824301 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (214079824301 / 4000000000000 : ℝ) ≤
      (-(3659625853224161050433 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (214079824301 / 4000000000000 : ℝ) = (214079824301 / 125000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (214079824301 / 125000000000 : ℝ) ≤
            (672544023650838949567 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (437698325677629 / 2000000000000000 : ℝ) ≤ Real.sqrt (191579824301 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (191579824301 / 4000000000000 : ℝ) ≤ (547122907097037 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (191579824301 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau151 :
    Real.arctan (547122907097037 / 2500000000000000 : ℝ) ≤
      (2154523321717564278481 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2154523321717564278481 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 547122907097037 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 547122907097037 : ℝ) =
              (547122907097037 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau151)
  have hz1 :
    (2500000000000000 / 547122907097037 : ℝ) ≤ 1 / Real.sqrt (191579824301 / 4000000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 547122907097037 : ℝ) = 1 / (547122907097037 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 145899441892543 : ℝ) ≤
      (1320633347875011933 / 4000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (191579824301 / 4000000000000 : ℝ) ≤
      (50000000000000 / 145899441892543 : ℝ) := by
    rw [show
        (50000000000000 / 145899441892543 : ℝ) =
          (3 / 40) / (437698325677629 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2154523321717564278481 / 10000000000000000000000 : ℝ)) -
        6 * (1320633347875011933 / 4000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (191579824301 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (191579824301 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((437698325677629 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2154523321717564278481 / 10000000000000000000000 : ℝ)) -
          6 * (1320633347875011933 / 4000000000000000000 : ℝ))) ≤
      Real.sqrt (191579824301 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (191579824301 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (191579824301 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_90 :
    ((47140272598544088727 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29207353403930246574293 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((109851083505783 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (432532407747580506091 / 2000000000000000000000 : ℝ)) -
              6 * (1644835690550822215319 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3089218700133 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3089218700133 / 64000000000000 : ℝ)) =
      Real.log (67089218700133 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3089218700133 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3449218700133 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (47140272598544088727 / 1000000000000000000000 : ℝ) ≤
      Real.log (67089218700133 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3449218700133 / 64000000000000 : ℝ) ≤
      (-(29207353403930246574293 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (3449218700133 / 64000000000000 : ℝ) = (3449218700133 / 2000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3449218700133 / 2000000000000 : ℝ) ≤
            (5450005611069753425707 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (109851083505783 / 500000000000000 : ℝ) ≤ Real.sqrt (3089218700133 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3089218700133 / 64000000000000 : ℝ) ≤ (2197021670115663 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3089218700133 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau152 :
    Real.arctan (2197021670115663 / 10000000000000000 : ℝ) ≤
      (432532407747580506091 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (432532407747580506091 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2197021670115663 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2197021670115663 : ℝ) =
              (2197021670115663 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau152)
  have hz1 :
    (10000000000000000 / 2197021670115663 : ℝ) ≤
      1 / Real.sqrt (3089218700133 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2197021670115663 : ℝ) =
          1 / (2197021670115663 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (12500000000000 / 36617027835261 : ℝ) ≤
      (1644835690550822215319 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3089218700133 / 64000000000000 : ℝ) ≤
      (12500000000000 / 36617027835261 : ℝ) := by
    rw [show
        (12500000000000 / 36617027835261 : ℝ) = (3 / 40) / (109851083505783 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (432532407747580506091 / 2000000000000000000000 : ℝ)) -
        6 * (1644835690550822215319 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3089218700133 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3089218700133 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((109851083505783 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (432532407747580506091 / 2000000000000000000000 : ℝ)) -
          6 * (1644835690550822215319 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3089218700133 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3089218700133 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3089218700133 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_91 :
    ((118742674312179046039 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29138181787976365168227 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((220551872138747 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2170766386127115701763 / 10000000000000000000000 : ℝ)) -
              6 * (655577508409682210587 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (62263204229 / 1280000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (62263204229 / 1280000000000 : ℝ)) =
      Real.log (1342263204229 / 1280000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((62263204229 / 1280000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69463204229 / 1280000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (118742674312179046039 / 2500000000000000000000 : ℝ) ≤
      Real.log (1342263204229 / 1280000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69463204229 / 1280000000000 : ℝ) ≤
      (-(29138181787976365168227 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (69463204229 / 1280000000000 : ℝ) = (69463204229 / 40000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69463204229 / 40000000000 : ℝ) ≤
            (5519177227023634831773 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (220551872138747 / 1000000000000000 : ℝ) ≤ Real.sqrt (62263204229 / 1280000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (62263204229 / 1280000000000 : ℝ) ≤ (2205518721387473 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (62263204229 / 1280000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau153 :
    Real.arctan (2205518721387473 / 10000000000000000 : ℝ) ≤
      (2170766386127115701763 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2170766386127115701763 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2205518721387473 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2205518721387473 : ℝ) =
              (2205518721387473 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau153)
  have hz1 :
    (10000000000000000 / 2205518721387473 : ℝ) ≤
      1 / Real.sqrt (62263204229 / 1280000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2205518721387473 : ℝ) =
          1 / (2205518721387473 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 220551872138747 : ℝ) ≤
      (655577508409682210587 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (62263204229 / 1280000000000 : ℝ) ≤
      (75000000000000 / 220551872138747 : ℝ) := by
    rw [show
        (75000000000000 / 220551872138747 : ℝ) =
          (3 / 40) / (220551872138747 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2170766386127115701763 / 10000000000000000000000 : ℝ)) -
        6 * (655577508409682210587 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (62263204229 / 1280000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (62263204229 / 1280000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((220551872138747 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2170766386127115701763 / 10000000000000000000000 : ℝ)) -
          6 * (655577508409682210587 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (62263204229 / 1280000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (62263204229 / 1280000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (62263204229 / 1280000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_92 :
    ((478537395924140096139 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1816842834888117217761 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2213983162046051 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (544709187640218728401 / 2500000000000000000000 : ℝ)) -
              6 * (25517418505229754007 / 78125000000000000000 : ℝ)))) ≤
      Vfield (3137101722767 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3137101722767 / 64000000000000 : ℝ)) =
      Real.log (67137101722767 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3137101722767 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3497101722767 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (478537395924140096139 / 10000000000000000000000 : ℝ) ≤
      Real.log (67137101722767 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3497101722767 / 64000000000000 : ℝ) ≤
      (-(1816842834888117217761 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (3497101722767 / 64000000000000 : ℝ) = (3497101722767 / 2000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3497101722767 / 2000000000000 : ℝ) ≤
            (349242103549382782239 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2213983162046051 / 10000000000000000 : ℝ) ≤ Real.sqrt (3137101722767 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3137101722767 / 64000000000000 : ℝ) ≤ (1106991581023027 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3137101722767 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau154 :
    Real.arctan (1106991581023027 / 5000000000000000 : ℝ) ≤
      (544709187640218728401 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (544709187640218728401 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1106991581023027 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1106991581023027 : ℝ) =
              (1106991581023027 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau154)
  have hz1 :
    (5000000000000000 / 1106991581023027 : ℝ) ≤
      1 / Real.sqrt (3137101722767 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1106991581023027 : ℝ) = 1 / (1106991581023027 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2213983162046051 : ℝ) ≤
      (25517418505229754007 / 78125000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3137101722767 / 64000000000000 : ℝ) ≤
      (750000000000000 / 2213983162046051 : ℝ) := by
    rw [show
        (750000000000000 / 2213983162046051 : ℝ) =
          (3 / 40) / (2213983162046051 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (544709187640218728401 / 2500000000000000000000 : ℝ)) -
        6 * (25517418505229754007 / 78125000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3137101722767 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3137101722767 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2213983162046051 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (544709187640218728401 / 2500000000000000000000 : ℝ)) -
          6 * (25517418505229754007 / 78125000000000000000 : ℝ))) ≤
      Real.sqrt (3137101722767 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3137101722767 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3137101722767 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_93 :
    ((241051411459588228539 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14500628815202590003913 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1111207682350181 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2186873511406957655783 / 10000000000000000000000 : ℝ)) -
              6 * (3254695233748423021389 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (790260808521 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (790260808521 / 16000000000000 : ℝ)) =
      Real.log (16790260808521 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((790260808521 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (880260808521 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (241051411459588228539 / 5000000000000000000000 : ℝ) ≤
      Real.log (16790260808521 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (880260808521 / 16000000000000 : ℝ) ≤
      (-(14500628815202590003913 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (880260808521 / 16000000000000 : ℝ) = (880260808521 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (880260808521 / 500000000000 : ℝ) ≤
            (2828050692297409996087 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1111207682350181 / 5000000000000000 : ℝ) ≤ Real.sqrt (790260808521 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (790260808521 / 16000000000000 : ℝ) ≤ (444483072940073 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (790260808521 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau155 :
    Real.arctan (444483072940073 / 2000000000000000 : ℝ) ≤
      (2186873511406957655783 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2186873511406957655783 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 444483072940073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 444483072940073 : ℝ) =
              (444483072940073 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau155)
  have hz1 :
    (2000000000000000 / 444483072940073 : ℝ) ≤
      1 / Real.sqrt (790260808521 / 16000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 444483072940073 : ℝ) = 1 / (444483072940073 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1111207682350181 : ℝ) ≤
      (3254695233748423021389 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (790260808521 / 16000000000000 : ℝ) ≤
      (375000000000000 / 1111207682350181 : ℝ) := by
    rw [show
        (375000000000000 / 1111207682350181 : ℝ) =
          (3 / 40) / (1111207682350181 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2186873511406957655783 / 10000000000000000000000 : ℝ)) -
        6 * (3254695233748423021389 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (790260808521 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (790260808521 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1111207682350181 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2186873511406957655783 / 10000000000000000000000 : ℝ)) -
          6 * (3254695233748423021389 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (790260808521 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (790260808521 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (790260808521 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_94 :
    ((7588546549067481217 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(361668653152000194621 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2230815694917233 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2194877040918014085383 / 10000000000000000000000 : ℝ)) -
              6 * (1621641182458017941551 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3184984745401 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3184984745401 / 64000000000000 : ℝ)) =
      Real.log (67184984745401 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3184984745401 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3544984745401 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (7588546549067481217 / 156250000000000000000 : ℝ) ≤
      Real.log (67184984745401 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3544984745401 / 64000000000000 : ℝ) ≤
      (-(361668653152000194621 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (3544984745401 / 64000000000000 : ℝ) = (3544984745401 / 2000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3544984745401 / 2000000000000 : ℝ) ≤
            (71548334535499805379 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2230815694917233 / 10000000000000000 : ℝ) ≤ Real.sqrt (3184984745401 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3184984745401 / 64000000000000 : ℝ) ≤ (557703923729309 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3184984745401 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau156 :
    Real.arctan (557703923729309 / 2500000000000000 : ℝ) ≤
      (2194877040918014085383 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2194877040918014085383 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 557703923729309 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 557703923729309 : ℝ) =
              (557703923729309 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau156)
  have hz1 :
    (2500000000000000 / 557703923729309 : ℝ) ≤
      1 / Real.sqrt (3184984745401 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 557703923729309 : ℝ) = 1 / (557703923729309 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2230815694917233 : ℝ) ≤
      (1621641182458017941551 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3184984745401 / 64000000000000 : ℝ) ≤
      (750000000000000 / 2230815694917233 : ℝ) := by
    rw [show
        (750000000000000 / 2230815694917233 : ℝ) =
          (3 / 40) / (2230815694917233 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2194877040918014085383 / 10000000000000000000000 : ℝ)) -
        6 * (1621641182458017941551 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3184984745401 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3184984745401 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2230815694917233 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2194877040918014085383 / 10000000000000000000000 : ℝ)) -
          6 * (1621641182458017941551 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3184984745401 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3184984745401 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3184984745401 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_95 :
    ((489229865493091729373 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14433091499673113264557 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((22391845114063 / 100000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1101423852208921727903 / 5000000000000000000000 : ℝ)) -
              6 * (807997210730837352441 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1604463128359 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1604463128359 / 32000000000000 : ℝ)) =
      Real.log (33604463128359 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1604463128359 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1784463128359 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (489229865493091729373 / 10000000000000000000000 : ℝ) ≤
      Real.log (33604463128359 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1784463128359 / 32000000000000 : ℝ) ≤
      (-(14433091499673113264557 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1784463128359 / 32000000000000 : ℝ) = (1784463128359 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1784463128359 / 1000000000000 : ℝ) ≤
            (2895588007826886735443 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (22391845114063 / 100000000000000 : ℝ) ≤ Real.sqrt (1604463128359 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1604463128359 / 32000000000000 : ℝ) ≤ (2239184511406303 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1604463128359 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau157 :
    Real.arctan (2239184511406303 / 10000000000000000 : ℝ) ≤
      (1101423852208921727903 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1101423852208921727903 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2239184511406303 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2239184511406303 : ℝ) =
              (2239184511406303 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau157)
  have hz1 :
    (10000000000000000 / 2239184511406303 : ℝ) ≤
      1 / Real.sqrt (1604463128359 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2239184511406303 : ℝ) =
          1 / (2239184511406303 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (7500000000000 / 22391845114063 : ℝ) ≤
      (807997210730837352441 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1604463128359 / 32000000000000 : ℝ) ≤
      (7500000000000 / 22391845114063 : ℝ) := by
    rw [show
        (7500000000000 / 22391845114063 : ℝ) = (3 / 40) / (22391845114063 / 100000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1101423852208921727903 / 5000000000000000000000 : ℝ)) -
        6 * (807997210730837352441 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1604463128359 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1604463128359 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((22391845114063 / 100000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1101423852208921727903 / 5000000000000000000000 : ℝ)) -
          6 * (807997210730837352441 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1604463128359 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1604463128359 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1604463128359 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_96 :
    ((123197870720513080647 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14399661886339595032899 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2247522166198741 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2210785860481439136199 / 10000000000000000000000 : ℝ)) -
              6 * (3220812599981731487411 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (646573553607 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (646573553607 / 12800000000000 : ℝ)) =
      Real.log (13446573553607 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((646573553607 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (718573553607 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (123197870720513080647 / 2500000000000000000000 : ℝ) ≤
      Real.log (13446573553607 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (718573553607 / 12800000000000 : ℝ) ≤
      (-(14399661886339595032899 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (718573553607 / 12800000000000 : ℝ) = (718573553607 / 400000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (718573553607 / 400000000000 : ℝ) ≤
            (2929017621160404967101 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2247522166198741 / 10000000000000000 : ℝ) ≤ Real.sqrt (646573553607 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (646573553607 / 12800000000000 : ℝ) ≤ (280940270774843 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (646573553607 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau158 :
    Real.arctan (280940270774843 / 1250000000000000 : ℝ) ≤
      (2210785860481439136199 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2210785860481439136199 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 280940270774843 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 280940270774843 : ℝ) =
              (280940270774843 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau158)
  have hz1 :
    (1250000000000000 / 280940270774843 : ℝ) ≤
      1 / Real.sqrt (646573553607 / 12800000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 280940270774843 : ℝ) = 1 / (280940270774843 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2247522166198741 : ℝ) ≤
      (3220812599981731487411 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (646573553607 / 12800000000000 : ℝ) ≤
      (750000000000000 / 2247522166198741 : ℝ) := by
    rw [show
        (750000000000000 / 2247522166198741 : ℝ) =
          (3 / 40) / (2247522166198741 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2210785860481439136199 / 10000000000000000000000 : ℝ)) -
        6 * (3220812599981731487411 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (646573553607 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (646573553607 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2247522166198741 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2210785860481439136199 / 10000000000000000000000 : ℝ)) -
          6 * (3220812599981731487411 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (646573553607 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (646573553607 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (646573553607 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
