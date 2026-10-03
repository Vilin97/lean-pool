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

/-! # V16: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_193 :
    ((1379119536463717589619 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1874058101002048808097 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1922722546692823 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3671120904872284070399 / 10000000000000000000000 : ℝ)) -
              6 * (1926179010437621127729 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2365991674599 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2365991674599 / 16000000000000 : ℝ)) =
      Real.log (18365991674599 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2365991674599 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2455991674599 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1379119536463717589619 / 10000000000000000000000 : ℝ) ≤
      Real.log (18365991674599 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2455991674599 / 16000000000000 : ℝ) ≤
      (-(1874058101002048808097 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2455991674599 / 16000000000000 : ℝ) = (2455991674599 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2455991674599 / 2000000000000 : ℝ) ≤
            (205383439897951191903 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1922722546692823 / 5000000000000000 : ℝ) ≤ Real.sqrt (2365991674599 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2365991674599 / 16000000000000 : ℝ) ≤ (3845445093385649 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2365991674599 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau255 :
    Real.arctan (3845445093385649 / 10000000000000000 : ℝ) ≤
      (3671120904872284070399 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3671120904872284070399 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3845445093385649 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3845445093385649 : ℝ) =
              (3845445093385649 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau255)
  have hz1 :
    (10000000000000000 / 3845445093385649 : ℝ) ≤
      1 / Real.sqrt (2365991674599 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3845445093385649 : ℝ) =
          1 / (3845445093385649 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1922722546692823 : ℝ) ≤
      (1926179010437621127729 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2365991674599 / 16000000000000 : ℝ) ≤
      (375000000000000 / 1922722546692823 : ℝ) := by
    rw [show
        (375000000000000 / 1922722546692823 : ℝ) =
          (3 / 40) / (1922722546692823 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3671120904872284070399 / 10000000000000000000000 : ℝ)) -
        6 * (1926179010437621127729 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2365991674599 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2365991674599 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1922722546692823 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3671120904872284070399 / 10000000000000000000000 : ℝ)) -
          6 * (1926179010437621127729 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2365991674599 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2365991674599 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2365991674599 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_194 :
    ((1394565529352076953773 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18625649088734036599843 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((120888982420927 / 312500000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (922786131046177653937 / 2500000000000000000000 : ℝ)) -
              6 * (1915004440272120860647 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4788763384469 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4788763384469 / 32000000000000 : ℝ)) =
      Real.log (36788763384469 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4788763384469 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4968763384469 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1394565529352076953773 / 10000000000000000000000 : ℝ) ≤
      Real.log (36788763384469 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4968763384469 / 32000000000000 : ℝ) ≤
      (-(18625649088734036599843 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4968763384469 / 32000000000000 : ℝ) = (4968763384469 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4968763384469 / 4000000000000 : ℝ) ≤
            (2168766320265963400157 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (120888982420927 / 312500000000000 : ℝ) ≤ Real.sqrt (4788763384469 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4788763384469 / 32000000000000 : ℝ) ≤ (3868447437469667 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4788763384469 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau256 :
    Real.arctan (3868447437469667 / 10000000000000000 : ℝ) ≤
      (922786131046177653937 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (922786131046177653937 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3868447437469667 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3868447437469667 : ℝ) =
              (3868447437469667 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau256)
  have hz1 :
    (10000000000000000 / 3868447437469667 : ℝ) ≤
      1 / Real.sqrt (4788763384469 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3868447437469667 : ℝ) =
          1 / (3868447437469667 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (23437500000000 / 120888982420927 : ℝ) ≤
      (1915004440272120860647 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4788763384469 / 32000000000000 : ℝ) ≤
      (23437500000000 / 120888982420927 : ℝ) := by
    rw [show
        (23437500000000 / 120888982420927 : ℝ) =
          (3 / 40) / (120888982420927 / 312500000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (922786131046177653937 / 2500000000000000000000 : ℝ)) -
        6 * (1915004440272120860647 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4788763384469 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4788763384469 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((120888982420927 / 312500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (922786131046177653937 / 2500000000000000000000 : ℝ)) -
          6 * (1915004440272120860647 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4788763384469 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4788763384469 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4788763384469 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_195 :
    ((175284948537260638459 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4642168678222045719597 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3879897470497971 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1850550138337685246867 / 5000000000000000000000 : ℝ)) -
              6 * (1909489605510279217527 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9634306804209 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9634306804209 / 64000000000000 : ℝ)) =
      Real.log (73634306804209 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9634306804209 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9994306804209 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (175284948537260638459 / 1250000000000000000000 : ℝ) ≤
      Real.log (73634306804209 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9994306804209 / 64000000000000 : ℝ) ≤
      (-(4642168678222045719597 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (9994306804209 / 64000000000000 : ℝ) = (9994306804209 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9994306804209 / 8000000000000 : ℝ) ≤
            (556435174027954280403 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3879897470497971 / 10000000000000000 : ℝ) ≤ Real.sqrt (9634306804209 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9634306804209 / 64000000000000 : ℝ) ≤ (1939948735248987 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9634306804209 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau257 :
    Real.arctan (1939948735248987 / 5000000000000000 : ℝ) ≤
      (1850550138337685246867 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1850550138337685246867 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1939948735248987 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1939948735248987 : ℝ) =
              (1939948735248987 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau257)
  have hz1 :
    (5000000000000000 / 1939948735248987 : ℝ) ≤
      1 / Real.sqrt (9634306804209 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1939948735248987 : ℝ) = 1 / (1939948735248987 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1293299156832657 : ℝ) ≤
      (1909489605510279217527 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9634306804209 / 64000000000000 : ℝ) ≤
      (250000000000000 / 1293299156832657 : ℝ) := by
    rw [show
        (250000000000000 / 1293299156832657 : ℝ) =
          (3 / 40) / (3879897470497971 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1850550138337685246867 / 5000000000000000000000 : ℝ)) -
        6 * (1909489605510279217527 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9634306804209 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9634306804209 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3879897470497971 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1850550138337685246867 / 5000000000000000000000 : ℝ)) -
          6 * (1909489605510279217527 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (9634306804209 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9634306804209 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9634306804209 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_196 :
    ((1409987701160100614743 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4628005776724920317491 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3891313812414451 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (742203816691221276071 / 2000000000000000000000 : ℝ)) -
              6 * (1904022148523259736843 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (242277170987 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (242277170987 / 1600000000000 : ℝ)) =
      Real.log (1842277170987 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((242277170987 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (251277170987 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1409987701160100614743 / 10000000000000000000000 : ℝ) ≤
      Real.log (1842277170987 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (251277170987 / 1600000000000 : ℝ) ≤
      (-(4628005776724920317491 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (251277170987 / 1600000000000 : ℝ) = (251277170987 / 200000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (251277170987 / 200000000000 : ℝ) ≤
            (570598075525079682509 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3891313812414451 / 10000000000000000 : ℝ) ≤ Real.sqrt (242277170987 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (242277170987 / 1600000000000 : ℝ) ≤ (1945656906207227 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (242277170987 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau258 :
    Real.arctan (1945656906207227 / 5000000000000000 : ℝ) ≤
      (742203816691221276071 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (742203816691221276071 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1945656906207227 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1945656906207227 : ℝ) =
              (1945656906207227 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau258)
  have hz1 :
    (5000000000000000 / 1945656906207227 : ℝ) ≤
      1 / Real.sqrt (242277170987 / 1600000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1945656906207227 : ℝ) = 1 / (1945656906207227 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3891313812414451 : ℝ) ≤
      (1904022148523259736843 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (242277170987 / 1600000000000 : ℝ) ≤
      (750000000000000 / 3891313812414451 : ℝ) := by
    rw [show
        (750000000000000 / 3891313812414451 : ℝ) =
          (3 / 40) / (3891313812414451 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (742203816691221276071 / 2000000000000000000000 : ℝ)) -
        6 * (1904022148523259736843 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (242277170987 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (242277170987 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3891313812414451 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (742203816691221276071 / 2000000000000000000000 : ℝ)) -
          6 * (1904022148523259736843 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (242277170987 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (242277170987 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (242277170987 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_197 :
    ((283537975419536278287 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18455690634264303292773 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3902696758883327 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (744180251624464067841 / 2000000000000000000000 : ℝ)) -
              6 * (1898601394724880011151 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9747866874751 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9747866874751 / 64000000000000 : ℝ)) =
      Real.log (73747866874751 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9747866874751 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10107866874751 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (283537975419536278287 / 2000000000000000000000 : ℝ) ≤
      Real.log (73747866874751 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10107866874751 / 64000000000000 : ℝ) ≤
      (-(18455690634264303292773 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (10107866874751 / 64000000000000 : ℝ) = (10107866874751 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10107866874751 / 8000000000000 : ℝ) ≤
            (2338724774735696707227 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3902696758883327 / 10000000000000000 : ℝ) ≤ Real.sqrt (9747866874751 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9747866874751 / 64000000000000 : ℝ) ≤ (390269675888333 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9747866874751 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau259 :
    Real.arctan (390269675888333 / 1000000000000000 : ℝ) ≤
      (744180251624464067841 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (744180251624464067841 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 390269675888333 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 390269675888333 : ℝ) =
              (390269675888333 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau259)
  have hz1 :
    (1000000000000000 / 390269675888333 : ℝ) ≤
      1 / Real.sqrt (9747866874751 / 64000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 390269675888333 : ℝ) = 1 / (390269675888333 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3902696758883327 : ℝ) ≤
      (1898601394724880011151 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9747866874751 / 64000000000000 : ℝ) ≤
      (750000000000000 / 3902696758883327 : ℝ) := by
    rw [show
        (750000000000000 / 3902696758883327 : ℝ) =
          (3 / 40) / (3902696758883327 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (744180251624464067841 / 2000000000000000000000 : ℝ)) -
        6 * (1898601394724880011151 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9747866874751 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9747866874751 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3902696758883327 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (744180251624464067841 / 2000000000000000000000 : ℝ)) -
          6 * (1898601394724880011151 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (9747866874751 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9747866874751 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9747866874751 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_198 :
    ((1425386125249237081831 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(73598694878360117537 / 40000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((782809320253901 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3730747109815750035747 / 10000000000000000000000 : ℝ)) -
              6 * (1893226682901490889443 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4902323455011 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4902323455011 / 32000000000000 : ℝ)) =
      Real.log (36902323455011 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4902323455011 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5082323455011 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1425386125249237081831 / 10000000000000000000000 : ℝ) ≤
      Real.log (36902323455011 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5082323455011 / 32000000000000 : ℝ) ≤
      (-(73598694878360117537 / 40000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5082323455011 / 32000000000000 : ℝ) = (5082323455011 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5082323455011 / 4000000000000 : ℝ) ≤
            (9578966757639882463 / 40000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (782809320253901 / 2000000000000000 : ℝ) ≤ Real.sqrt (4902323455011 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4902323455011 / 32000000000000 : ℝ) ≤ (978511650317377 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4902323455011 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau260 :
    Real.arctan (978511650317377 / 2500000000000000 : ℝ) ≤
      (3730747109815750035747 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3730747109815750035747 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 978511650317377 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 978511650317377 : ℝ) =
              (978511650317377 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau260)
  have hz1 :
    (2500000000000000 / 978511650317377 : ℝ) ≤
      1 / Real.sqrt (4902323455011 / 32000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 978511650317377 : ℝ) = 1 / (978511650317377 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 782809320253901 : ℝ) ≤
      (1893226682901490889443 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4902323455011 / 32000000000000 : ℝ) ≤
      (150000000000000 / 782809320253901 : ℝ) := by
    rw [show
        (150000000000000 / 782809320253901 : ℝ) =
          (3 / 40) / (782809320253901 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3730747109815750035747 / 10000000000000000000000 : ℝ)) -
        6 * (1893226682901490889443 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4902323455011 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4902323455011 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((782809320253901 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3730747109815750035747 / 10000000000000000000000 : ℝ)) -
          6 * (1893226682901490889443 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4902323455011 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4902323455011 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4902323455011 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_199 :
    ((716538227366047056267 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18343968847235335596581 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3925363626725593 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (935139235828401014473 / 2500000000000000000000 : ℝ)) -
              6 * (47197434121825702827 / 250000000000000000000 : ℝ)))) ≤
      Vfield (9861426945293 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9861426945293 / 64000000000000 : ℝ)) =
      Real.log (73861426945293 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9861426945293 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10221426945293 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (716538227366047056267 / 5000000000000000000000 : ℝ) ≤
      Real.log (73861426945293 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10221426945293 / 64000000000000 : ℝ) ≤
      (-(18343968847235335596581 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (10221426945293 / 64000000000000 : ℝ) = (10221426945293 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10221426945293 / 8000000000000 : ℝ) ≤
            (2450446561764664403419 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3925363626725593 / 10000000000000000 : ℝ) ≤ Real.sqrt (9861426945293 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9861426945293 / 64000000000000 : ℝ) ≤ (981340906681399 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9861426945293 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau261 :
    Real.arctan (981340906681399 / 2500000000000000 : ℝ) ≤
      (935139235828401014473 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (935139235828401014473 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 981340906681399 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 981340906681399 : ℝ) =
              (981340906681399 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau261)
  have hz1 :
    (2500000000000000 / 981340906681399 : ℝ) ≤
      1 / Real.sqrt (9861426945293 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 981340906681399 : ℝ) = 1 / (981340906681399 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3925363626725593 : ℝ) ≤
      (47197434121825702827 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9861426945293 / 64000000000000 : ℝ) ≤
      (750000000000000 / 3925363626725593 : ℝ) := by
    rw [show
        (750000000000000 / 3925363626725593 : ℝ) =
          (3 / 40) / (3925363626725593 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (935139235828401014473 / 2500000000000000000000 : ℝ)) -
        6 * (47197434121825702827 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9861426945293 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9861426945293 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3925363626725593 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (935139235828401014473 / 2500000000000000000000 : ℝ)) -
          6 * (47197434121825702827 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (9861426945293 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9861426945293 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9861426945293 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_200 :
    ((360190218660640124399 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(914428627999259877791 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3936648118276669 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (468791382389424016227 / 1250000000000000000000 : ℝ)) -
              6 * (117663300322781655899 / 625000000000000000000 : ℝ)))) ≤
      Vfield (2479551745141 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2479551745141 / 16000000000000 : ℝ)) =
      Real.log (18479551745141 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2479551745141 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2569551745141 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (360190218660640124399 / 2500000000000000000000 : ℝ) ≤
      Real.log (18479551745141 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2569551745141 / 16000000000000 : ℝ) ≤
      (-(914428627999259877791 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2569551745141 / 16000000000000 : ℝ) = (2569551745141 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2569551745141 / 2000000000000 : ℝ) ≤
            (125292142450740122209 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3936648118276669 / 10000000000000000 : ℝ) ≤ Real.sqrt (2479551745141 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2479551745141 / 16000000000000 : ℝ) ≤ (61510126848073 / 156250000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2479551745141 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau262 :
    Real.arctan (61510126848073 / 156250000000000 : ℝ) ≤
      (468791382389424016227 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (468791382389424016227 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (156250000000000 / 61510126848073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (156250000000000 / 61510126848073 : ℝ) =
              (61510126848073 / 156250000000000 : ℝ)
            by
        norm_num];
        exact hau262)
  have hz1 :
    (156250000000000 / 61510126848073 : ℝ) ≤ 1 / Real.sqrt (2479551745141 / 16000000000000 : ℝ) :=
  by
    rw [show (156250000000000 / 61510126848073 : ℝ) = 1 / (61510126848073 / 156250000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3936648118276669 : ℝ) ≤
      (117663300322781655899 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2479551745141 / 16000000000000 : ℝ) ≤
      (750000000000000 / 3936648118276669 : ℝ) := by
    rw [show
        (750000000000000 / 3936648118276669 : ℝ) =
          (3 / 40) / (3936648118276669 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (468791382389424016227 / 1250000000000000000000 : ℝ)) -
        6 * (117663300322781655899 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2479551745141 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2479551745141 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3936648118276669 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (468791382389424016227 / 1250000000000000000000 : ℝ)) -
          6 * (117663300322781655899 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (2479551745141 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2479551745141 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2479551745141 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_201 :
    ((722300435672506061083 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18260989071053057397457 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((394227825117491 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3755204815637543892277 / 10000000000000000000000 : ℝ)) -
              6 * (1879987114489769237383 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19893193996399 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19893193996399 / 128000000000000 : ℝ)) =
      Real.log (147893193996399 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19893193996399 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20613193996399 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (722300435672506061083 / 5000000000000000000000 : ℝ) ≤
      Real.log (147893193996399 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20613193996399 / 128000000000000 : ℝ) ≤
      (-(18260989071053057397457 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (20613193996399 / 128000000000000 : ℝ) = (20613193996399 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20613193996399 / 16000000000000 : ℝ) ≤
            (2533426337946942602543 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (394227825117491 / 1000000000000000 : ℝ) ≤ Real.sqrt (19893193996399 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19893193996399 / 128000000000000 : ℝ) ≤
      (3942278251174913 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19893193996399 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau263 :
    Real.arctan (3942278251174913 / 10000000000000000 : ℝ) ≤
      (3755204815637543892277 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3755204815637543892277 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3942278251174913 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3942278251174913 : ℝ) =
              (3942278251174913 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau263)
  have hz1 :
    (10000000000000000 / 3942278251174913 : ℝ) ≤
      1 / Real.sqrt (19893193996399 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3942278251174913 : ℝ) =
          1 / (3942278251174913 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 394227825117491 : ℝ) ≤
      (1879987114489769237383 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19893193996399 / 128000000000000 : ℝ) ≤
      (75000000000000 / 394227825117491 : ℝ) := by
    rw [show
        (75000000000000 / 394227825117491 : ℝ) =
          (3 / 40) / (394227825117491 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3755204815637543892277 / 10000000000000000000000 : ℝ)) -
        6 * (1879987114489769237383 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19893193996399 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19893193996399 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((394227825117491 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3755204815637543892277 / 10000000000000000000000 : ℝ)) -
          6 * (1879987114489769237383 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (19893193996399 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19893193996399 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19893193996399 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_202 :
    ((1448439394055990394649 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18233481457763565163467 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1973950177451433 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3760069753527545238699 / 10000000000000000000000 : ℝ)) -
              6 * (187737238068757978517 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (1994997403167 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1994997403167 / 12800000000000 : ℝ)) =
      Real.log (14794997403167 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1994997403167 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2066997403167 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1448439394055990394649 / 10000000000000000000000 : ℝ) ≤
      Real.log (14794997403167 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2066997403167 / 12800000000000 : ℝ) ≤
      (-(18233481457763565163467 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2066997403167 / 12800000000000 : ℝ) = (2066997403167 / 1600000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2066997403167 / 1600000000000 : ℝ) ≤
            (2560933951236434836533 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1973950177451433 / 5000000000000000 : ℝ) ≤ Real.sqrt (1994997403167 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1994997403167 / 12800000000000 : ℝ) ≤ (3947900354902869 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1994997403167 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau264 :
    Real.arctan (3947900354902869 / 10000000000000000 : ℝ) ≤
      (3760069753527545238699 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3760069753527545238699 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3947900354902869 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3947900354902869 : ℝ) =
              (3947900354902869 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau264)
  have hz1 :
    (10000000000000000 / 3947900354902869 : ℝ) ≤
      1 / Real.sqrt (1994997403167 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3947900354902869 : ℝ) =
          1 / (3947900354902869 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 657983392483811 : ℝ) ≤
      (187737238068757978517 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1994997403167 / 12800000000000 : ℝ) ≤
      (125000000000000 / 657983392483811 : ℝ) := by
    rw [show
        (125000000000000 / 657983392483811 : ℝ) =
          (3 / 40) / (1973950177451433 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3760069753527545238699 / 10000000000000000000000 : ℝ)) -
        6 * (187737238068757978517 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1994997403167 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1994997403167 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1973950177451433 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3760069753527545238699 / 10000000000000000000000 : ℝ)) -
          6 * (187737238068757978517 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (1994997403167 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1994997403167 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1994997403167 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_203 :
    ((1452276443906651095289 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18206049303829734797543 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1976757231857117 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1882462954591030446627 / 5000000000000000000000 : ℝ)) -
              6 * (937384263878327770559 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (20006754066941 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20006754066941 / 128000000000000 : ℝ)) =
      Real.log (148006754066941 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20006754066941 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20726754066941 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1452276443906651095289 / 10000000000000000000000 : ℝ) ≤
      Real.log (148006754066941 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20726754066941 / 128000000000000 : ℝ) ≤
      (-(18206049303829734797543 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (20726754066941 / 128000000000000 : ℝ) = (20726754066941 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20726754066941 / 16000000000000 : ℝ) ≤
            (2588366105170265202457 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1976757231857117 / 5000000000000000 : ℝ) ≤
      Real.sqrt (20006754066941 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20006754066941 / 128000000000000 : ℝ) ≤
      (3953514463714237 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20006754066941 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau265 :
    Real.arctan (3953514463714237 / 10000000000000000 : ℝ) ≤
      (1882462954591030446627 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1882462954591030446627 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3953514463714237 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3953514463714237 : ℝ) =
              (3953514463714237 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau265)
  have hz1 :
    (10000000000000000 / 3953514463714237 : ℝ) ≤
      1 / Real.sqrt (20006754066941 / 128000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3953514463714237 : ℝ) =
          1 / (3953514463714237 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1976757231857117 : ℝ) ≤
      (937384263878327770559 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20006754066941 / 128000000000000 : ℝ) ≤
      (375000000000000 / 1976757231857117 : ℝ) := by
    rw [show
        (375000000000000 / 1976757231857117 : ℝ) =
          (3 / 40) / (1976757231857117 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1882462954591030446627 / 5000000000000000000000 : ℝ)) -
        6 * (937384263878327770559 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20006754066941 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20006754066941 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1976757231857117 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1882462954591030446627 / 5000000000000000000000 : ℝ)) -
          6 * (937384263878327770559 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (20006754066941 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20006754066941 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20006754066941 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_204 :
    ((145611202202684841337 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18178692196381109013093 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3959120611619847 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3769773318745880151089 / 10000000000000000000000 : ℝ)) -
              6 * (1872175480431801522837 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5015883525553 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5015883525553 / 32000000000000 : ℝ)) =
      Real.log (37015883525553 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5015883525553 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5195883525553 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (145611202202684841337 / 1000000000000000000000 : ℝ) ≤
      Real.log (37015883525553 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5195883525553 / 32000000000000 : ℝ) ≤
      (-(18178692196381109013093 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5195883525553 / 32000000000000 : ℝ) = (5195883525553 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5195883525553 / 4000000000000 : ℝ) ≤
            (2615723212618890986907 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3959120611619847 / 10000000000000000 : ℝ) ≤ Real.sqrt (5015883525553 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5015883525553 / 32000000000000 : ℝ) ≤ (79182412232397 / 200000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5015883525553 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau266 :
    Real.arctan (79182412232397 / 200000000000000 : ℝ) ≤
      (3769773318745880151089 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3769773318745880151089 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (200000000000000 / 79182412232397 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 79182412232397 : ℝ) =
              (79182412232397 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau266)
  have hz1 :
    (200000000000000 / 79182412232397 : ℝ) ≤ 1 / Real.sqrt (5015883525553 / 32000000000000 : ℝ) :=
  by
    rw [show (200000000000000 / 79182412232397 : ℝ) = 1 / (79182412232397 / 200000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1319706870539949 : ℝ) ≤
      (1872175480431801522837 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5015883525553 / 32000000000000 : ℝ) ≤
      (250000000000000 / 1319706870539949 : ℝ) := by
    rw [show
        (250000000000000 / 1319706870539949 : ℝ) =
          (3 / 40) / (3959120611619847 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3769773318745880151089 / 10000000000000000000000 : ℝ)) -
        6 * (1872175480431801522837 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5015883525553 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5015883525553 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3959120611619847 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3769773318745880151089 / 10000000000000000000000 : ℝ)) -
          6 * (1872175480431801522837 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5015883525553 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5015883525553 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5015883525553 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
