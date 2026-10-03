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

/-! # V49: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_589 :
    ((5210003340544330517601 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3720263456569547413113 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8268682368393859 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3454553289605606480941 / 10000000000000000000000 : ℝ))) -
              6 * (452280829327876491589 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (5469688648751 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5469688648751 / 8000000000000 : ℝ)) =
      Real.log (13469688648751 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5469688648751 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5514688648751 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5210003340544330517601 / 10000000000000000000000 : ℝ) ≤
      Real.log (13469688648751 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5514688648751 / 8000000000000 : ℝ) ≤
      (-(3720263456569547413113 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5514688648751 / 8000000000000 : ℝ) = (5514688648751 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5514688648751 / 4000000000000 : ℝ) ≤
            (3211208346430452586887 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8268682368393859 / 10000000000000000 : ℝ) ≤ Real.sqrt (5469688648751 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5469688648751 / 8000000000000 : ℝ) ≤ (4134341184196931 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5469688648751 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau950 :
    Real.arctan (4134341184196931 / 11487894652916836 : ℝ) ≤
      (3454553289605606480941 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau949 :
    Real.arctan (4134341184196931 / 5000000000000000 : ℝ) ≤
      (2 * (3454553289605606480941 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1621973663229209 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (4134341184196931 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4134341184196931 / 5000000000000000 : ℝ) /
                (1 + (1621973663229209 / 1250000000000000 : ℝ)) =
              (4134341184196931 / 11487894652916836 : ℝ)
            by
        norm_num];
        exact hau950)
  have hat1 :
    (Real.pi / 2 - (2 * (3454553289605606480941 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4134341184196931 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4134341184196931 : ℝ) =
              (4134341184196931 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau949)
  have hz1 :
    (5000000000000000 / 4134341184196931 : ℝ) ≤
      1 / Real.sqrt (5469688648751 / 8000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4134341184196931 : ℝ) = 1 / (4134341184196931 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8268682368393859 : ℝ) ≤
      (452280829327876491589 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5469688648751 / 8000000000000 : ℝ) ≤
      (750000000000000 / 8268682368393859 : ℝ) := by
    rw [show
        (750000000000000 / 8268682368393859 : ℝ) =
          (3 / 40) / (8268682368393859 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3454553289605606480941 / 10000000000000000000000 : ℝ))) -
        6 * (452280829327876491589 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5469688648751 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5469688648751 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8268682368393859 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3454553289605606480941 / 10000000000000000000000 : ℝ))) -
          6 * (452280829327876491589 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (5469688648751 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5469688648751 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5469688648751 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_590 :
    ((1303705082763694364061 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(370850198855605597403 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4136793197920123 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (138240370157103788799 / 400000000000000000000 : ℝ))) -
              6 * (452014206241029862917 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (43809428383637 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43809428383637 / 64000000000000 : ℝ)) =
      Real.log (107809428383637 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43809428383637 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (44169428383637 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1303705082763694364061 / 2500000000000000000000 : ℝ) ≤
      Real.log (107809428383637 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (44169428383637 / 64000000000000 : ℝ) ≤
      (-(370850198855605597403 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44169428383637 / 64000000000000 : ℝ) = (44169428383637 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44169428383637 / 32000000000000 : ℝ) ≤
            (322296981444394402597 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4136793197920123 / 5000000000000000 : ℝ) ≤ Real.sqrt (43809428383637 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43809428383637 / 64000000000000 : ℝ) ≤
      (8273586395840249 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43809428383637 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau952 :
    Real.arctan (285296082615181 / 792376375686706 : ℝ) ≤
      (138240370157103788799 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau951 :
    Real.arctan (8273586395840249 / 10000000000000000 : ℝ) ≤
      (2 * (138240370157103788799 / 400000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6489457447457237 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8273586395840249 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8273586395840249 / 10000000000000000 : ℝ) /
                (1 + (6489457447457237 / 5000000000000000 : ℝ)) =
              (285296082615181 / 792376375686706 : ℝ)
            by
        norm_num];
        exact hau952)
  have hat1 :
    (Real.pi / 2 - (2 * (138240370157103788799 / 400000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8273586395840249 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8273586395840249 : ℝ) =
              (8273586395840249 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau951)
  have hz1 :
    (10000000000000000 / 8273586395840249 : ℝ) ≤
      1 / Real.sqrt (43809428383637 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8273586395840249 : ℝ) =
          1 / (8273586395840249 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4136793197920123 : ℝ) ≤
      (452014206241029862917 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43809428383637 / 64000000000000 : ℝ) ≤
      (375000000000000 / 4136793197920123 : ℝ) := by
    rw [show
        (375000000000000 / 4136793197920123 : ℝ) =
          (3 / 40) / (4136793197920123 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (138240370157103788799 / 400000000000000000000 : ℝ))) -
        6 * (452014206241029862917 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43809428383637 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43809428383637 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4136793197920123 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (138240370157103788799 / 400000000000000000000 : ℝ))) -
          6 * (452014206241029862917 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (43809428383637 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43809428383637 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43809428383637 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_591 :
    ((521963500234258913999 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(924188584376590225871 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8278487518229287 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (86436591379470589641 / 250000000000000000000 : ℝ))) -
              6 * (903496108261826234217 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (21930673788633 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21930673788633 / 32000000000000 : ℝ)) =
      Real.log (53930673788633 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21930673788633 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22110673788633 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (521963500234258913999 / 1000000000000000000000 : ℝ) ≤
      Real.log (53930673788633 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22110673788633 / 32000000000000 : ℝ) ≤
      (-(924188584376590225871 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22110673788633 / 32000000000000 : ℝ) = (22110673788633 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22110673788633 / 16000000000000 : ℝ) ≤
            (808679366373409774129 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8278487518229287 / 10000000000000000 : ℝ) ≤
      Real.sqrt (21930673788633 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21930673788633 / 32000000000000 : ℝ) ≤ (827848751822929 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21930673788633 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau954 :
    Real.arctan (8278487518229290 / 22982039731470479 : ℝ) ≤
      (86436591379470589641 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau953 :
    Real.arctan (827848751822929 / 1000000000000000 : ℝ) ≤
      (2 * (86436591379470589641 / 250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12982039731470479 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (827848751822929 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (827848751822929 / 1000000000000000 : ℝ) /
                (1 + (12982039731470479 / 10000000000000000 : ℝ)) =
              (8278487518229290 / 22982039731470479 : ℝ)
            by
        norm_num];
        exact hau954)
  have hat1 :
    (Real.pi / 2 - (2 * (86436591379470589641 / 250000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 827848751822929 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 827848751822929 : ℝ) =
              (827848751822929 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau953)
  have hz1 :
    (1000000000000000 / 827848751822929 : ℝ) ≤
      1 / Real.sqrt (21930673788633 / 32000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 827848751822929 : ℝ) = 1 / (827848751822929 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8278487518229287 : ℝ) ≤
      (903496108261826234217 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21930673788633 / 32000000000000 : ℝ) ≤
      (750000000000000 / 8278487518229287 : ℝ) := by
    rw [show
        (750000000000000 / 8278487518229287 : ℝ) =
          (3 / 40) / (8278487518229287 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (86436591379470589641 / 250000000000000000000 : ℝ))) -
        6 * (903496108261826234217 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21930673788633 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21930673788633 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8278487518229287 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (86436591379470589641 / 250000000000000000000 : ℝ))) -
          6 * (903496108261826234217 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (21930673788633 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21930673788633 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21930673788633 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_592 :
    ((5224447356639949858109 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(737004094199034598467 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1656677148143517 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (345891649639318181503 / 1000000000000000000000 : ℝ))) -
              6 * (180592948645021209329 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (8782653354179 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8782653354179 / 12800000000000 : ℝ)) =
      Real.log (21582653354179 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8782653354179 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8854653354179 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5224447356639949858109 / 10000000000000000000000 : ℝ) ≤
      Real.log (21582653354179 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8854653354179 / 12800000000000 : ℝ) ≤
      (-(737004094199034598467 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8854653354179 / 12800000000000 : ℝ) = (8854653354179 / 6400000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8854653354179 / 6400000000000 : ℝ) ≤
            (649290266400965401533 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1656677148143517 / 2000000000000000 : ℝ) ≤ Real.sqrt (8782653354179 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8782653354179 / 12800000000000 : ℝ) ≤ (2070846435179397 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8782653354179 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau956 :
    Real.arctan (8283385740717588 / 22985163816044965 : ℝ) ≤
      (345891649639318181503 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau955 :
    Real.arctan (2070846435179397 / 2500000000000000 : ℝ) ≤
      (2 * (345891649639318181503 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2597032763208993 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2070846435179397 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2070846435179397 / 2500000000000000 : ℝ) /
                (1 + (2597032763208993 / 2000000000000000 : ℝ)) =
              (8283385740717588 / 22985163816044965 : ℝ)
            by
        norm_num];
        exact hau956)
  have hat1 :
    (Real.pi / 2 - (2 * (345891649639318181503 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2070846435179397 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2070846435179397 : ℝ) =
              (2070846435179397 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau955)
  have hz1 :
    (2500000000000000 / 2070846435179397 : ℝ) ≤
      1 / Real.sqrt (8782653354179 / 12800000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2070846435179397 : ℝ) = 1 / (2070846435179397 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 552225716047839 : ℝ) ≤
      (180592948645021209329 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8782653354179 / 12800000000000 : ℝ) ≤
      (50000000000000 / 552225716047839 : ℝ) := by
    rw [show
        (50000000000000 / 552225716047839 : ℝ) =
          (3 / 40) / (1656677148143517 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (345891649639318181503 / 1000000000000000000000 : ℝ))) -
        6 * (180592948645021209329 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8782653354179 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8782653354179 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1656677148143517 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (345891649639318181503 / 1000000000000000000000 : ℝ))) -
          6 * (180592948645021209329 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (8782653354179 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8782653354179 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8782653354179 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_593 :
    ((2614628698087911415639 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14693201426844845997 / 40000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1036035133555813 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3460367780595662617999 / 10000000000000000000000 : ℝ))) -
              6 * (180486862922668628021 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (10991296491131 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10991296491131 / 16000000000000 : ℝ)) =
      Real.log (26991296491131 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10991296491131 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11081296491131 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2614628698087911415639 / 5000000000000000000000 : ℝ) ≤
      Real.log (26991296491131 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11081296491131 / 16000000000000 : ℝ) ≤
      (-(14693201426844845997 / 40000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11081296491131 / 16000000000000 : ℝ) = (11081296491131 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11081296491131 / 8000000000000 : ℝ) ≤
            (13032685785155154003 / 40000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1036035133555813 / 1250000000000000 : ℝ) ≤ Real.sqrt (10991296491131 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10991296491131 / 16000000000000 : ℝ) ≤
      (8288281068446507 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10991296491131 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau958 :
    Real.arctan (8288281068446507 / 22988287149180554 : ℝ) ≤
      (3460367780595662617999 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau957 :
    Real.arctan (8288281068446507 / 10000000000000000 : ℝ) ≤
      (2 * (3460367780595662617999 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6494143574590277 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8288281068446507 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8288281068446507 / 10000000000000000 : ℝ) /
                (1 + (6494143574590277 / 5000000000000000 : ℝ)) =
              (8288281068446507 / 22988287149180554 : ℝ)
            by
        norm_num];
        exact hau958)
  have hat1 :
    (Real.pi / 2 - (2 * (3460367780595662617999 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8288281068446507 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8288281068446507 : ℝ) =
              (8288281068446507 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau957)
  have hz1 :
    (10000000000000000 / 8288281068446507 : ℝ) ≤
      1 / Real.sqrt (10991296491131 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8288281068446507 : ℝ) =
          1 / (8288281068446507 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 1036035133555813 : ℝ) ≤
      (180486862922668628021 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10991296491131 / 16000000000000 : ℝ) ≤
      (93750000000000 / 1036035133555813 : ℝ) := by
    rw [show
        (93750000000000 / 1036035133555813 : ℝ) =
          (3 / 40) / (1036035133555813 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3460367780595662617999 / 10000000000000000000000 : ℝ))) -
        6 * (180486862922668628021 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10991296491131 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10991296491131 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1036035133555813 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3460367780595662617999 / 10000000000000000000000 : ℝ))) -
          6 * (180486862922668628021 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (10991296491131 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10991296491131 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10991296491131 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_594 :
    ((654258140396994550749 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3661593962456670299233 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1658634701308447 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (216363594425149969639 / 625000000000000000000 : ℝ))) -
              6 * (901904819679311450819 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (44017105158153 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (44017105158153 / 64000000000000 : ℝ)) =
      Real.log (108017105158153 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((44017105158153 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (44377105158153 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (654258140396994550749 / 1250000000000000000000 : ℝ) ≤
      Real.log (108017105158153 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (44377105158153 / 64000000000000 : ℝ) ≤
      (-(3661593962456670299233 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44377105158153 / 64000000000000 : ℝ) = (44377105158153 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44377105158153 / 32000000000000 : ℝ) ≤
            (3269877840543329700767 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1658634701308447 / 2000000000000000 : ℝ) ≤ Real.sqrt (44017105158153 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (44017105158153 / 64000000000000 : ℝ) ≤ (4146586753271119 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (44017105158153 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau960 :
    Real.arctan (8293173506542238 / 22991409731419221 : ℝ) ≤
      (216363594425149969639 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau959 :
    Real.arctan (4146586753271119 / 5000000000000000 : ℝ) ≤
      (2 * (216363594425149969639 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12991409731419221 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4146586753271119 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4146586753271119 / 5000000000000000 : ℝ) /
                (1 + (12991409731419221 / 10000000000000000 : ℝ)) =
              (8293173506542238 / 22991409731419221 : ℝ)
            by
        norm_num];
        exact hau960)
  have hat1 :
    (Real.pi / 2 - (2 * (216363594425149969639 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4146586753271119 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4146586753271119 : ℝ) =
              (4146586753271119 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau959)
  have hz1 :
    (5000000000000000 / 4146586753271119 : ℝ) ≤
      1 / Real.sqrt (44017105158153 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4146586753271119 : ℝ) = 1 / (4146586753271119 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1658634701308447 : ℝ) ≤
      (901904819679311450819 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (44017105158153 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1658634701308447 : ℝ) := by
    rw [show
        (150000000000000 / 1658634701308447 : ℝ) =
          (3 / 40) / (1658634701308447 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (216363594425149969639 / 625000000000000000000 : ℝ))) -
        6 * (901904819679311450819 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (44017105158153 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (44017105158153 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1658634701308447 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (216363594425149969639 / 625000000000000000000 : ℝ))) -
          6 * (901904819679311450819 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (44017105158153 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (44017105158153 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (44017105158153 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_595 :
    ((1047774107972578046817 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(729980251229337430647 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4149031530057929 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3463265690020702793097 / 10000000000000000000000 : ℝ))) -
              6 * (901376255687055180941 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22034512175891 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22034512175891 / 32000000000000 : ℝ)) =
      Real.log (54034512175891 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22034512175891 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22214512175891 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1047774107972578046817 / 2000000000000000000000 : ℝ) ≤
      Real.log (54034512175891 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22214512175891 / 32000000000000 : ℝ) ≤
      (-(729980251229337430647 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22214512175891 / 32000000000000 : ℝ) = (22214512175891 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22214512175891 / 16000000000000 : ℝ) ≤
            (656314109370662569353 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4149031530057929 / 5000000000000000 : ℝ) ≤ Real.sqrt (22034512175891 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22034512175891 / 32000000000000 : ℝ) ≤
      (8298063060115861 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22034512175891 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau962 :
    Real.arctan (8298063060115861 / 22994531563302287 : ℝ) ≤
      (3463265690020702793097 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau961 :
    Real.arctan (8298063060115861 / 10000000000000000 : ℝ) ≤
      (2 * (3463265690020702793097 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12994531563302287 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8298063060115861 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8298063060115861 / 10000000000000000 : ℝ) /
                (1 + (12994531563302287 / 10000000000000000 : ℝ)) =
              (8298063060115861 / 22994531563302287 : ℝ)
            by
        norm_num];
        exact hau962)
  have hat1 :
    (Real.pi / 2 - (2 * (3463265690020702793097 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8298063060115861 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8298063060115861 : ℝ) =
              (8298063060115861 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau961)
  have hz1 :
    (10000000000000000 / 8298063060115861 : ℝ) ≤
      1 / Real.sqrt (22034512175891 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8298063060115861 : ℝ) =
          1 / (8298063060115861 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4149031530057929 : ℝ) ≤
      (901376255687055180941 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22034512175891 / 32000000000000 : ℝ) ≤
      (375000000000000 / 4149031530057929 : ℝ) := by
    rw [show
        (375000000000000 / 4149031530057929 : ℝ) =
          (3 / 40) / (4149031530057929 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3463265690020702793097 / 10000000000000000000000 : ℝ))) -
        6 * (901376255687055180941 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22034512175891 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22034512175891 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4149031530057929 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3463265690020702793097 / 10000000000000000000000 : ℝ))) -
          6 * (901376255687055180941 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22034512175891 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22034512175891 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22034512175891 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_596 :
    ((2621836824227980718709 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(727644441161763215397 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((41514748671317 / 50000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1732356160624546634617 / 5000000000000000000000 : ℝ))) -
              6 * (900848619911829885433 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (44120943545411 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (44120943545411 / 64000000000000 : ℝ)) =
      Real.log (108120943545411 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((44120943545411 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (44480943545411 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2621836824227980718709 / 5000000000000000000000 : ℝ) ≤
      Real.log (108120943545411 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (44480943545411 / 64000000000000 : ℝ) ≤
      (-(727644441161763215397 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44480943545411 / 64000000000000 : ℝ) = (44480943545411 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44480943545411 / 32000000000000 : ℝ) ≤
            (658649919438236784603 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (41514748671317 / 50000000000000 : ℝ) ≤ Real.sqrt (44120943545411 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (44120943545411 / 64000000000000 : ℝ) ≤
      (8302949734263403 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (44120943545411 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau964 :
    Real.arctan (8302949734263403 / 22997652645370420 : ℝ) ≤
      (1732356160624546634617 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau963 :
    Real.arctan (8302949734263403 / 10000000000000000 : ℝ) ≤
      (2 * (1732356160624546634617 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (649882632268521 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8302949734263403 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8302949734263403 / 10000000000000000 : ℝ) /
                (1 + (649882632268521 / 500000000000000 : ℝ)) =
              (8302949734263403 / 22997652645370420 : ℝ)
            by
        norm_num];
        exact hau964)
  have hat1 :
    (Real.pi / 2 - (2 * (1732356160624546634617 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8302949734263403 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8302949734263403 : ℝ) =
              (8302949734263403 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau963)
  have hz1 :
    (10000000000000000 / 8302949734263403 : ℝ) ≤
      1 / Real.sqrt (44120943545411 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8302949734263403 : ℝ) =
          1 / (8302949734263403 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (3750000000000 / 41514748671317 : ℝ) ≤
      (900848619911829885433 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (44120943545411 / 64000000000000 : ℝ) ≤
      (3750000000000 / 41514748671317 : ℝ) := by
    rw [show
        (3750000000000 / 41514748671317 : ℝ) = (3 / 40) / (41514748671317 / 50000000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1732356160624546634617 / 5000000000000000000000 : ℝ))) -
        6 * (900848619911829885433 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (44120943545411 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (44120943545411 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((41514748671317 / 50000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1732356160624546634617 / 5000000000000000000000 : ℝ))) -
          6 * (900848619911829885433 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (44120943545411 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (44120943545411 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (44120943545411 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_597 :
    ((5248474451171310757761 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(453319597447812848417 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((519239595879119 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (69323148149546782071 / 200000000000000000000 : ℝ))) -
              6 * (225080477410010679099 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (276080392119 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (276080392119 / 400000000000 : ℝ)) =
      Real.log (676080392119 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((276080392119 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (278330392119 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5248474451171310757761 / 10000000000000000000000 : ℝ) ≤
      Real.log (676080392119 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (278330392119 / 400000000000 : ℝ) ≤
      (-(453319597447812848417 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (278330392119 / 400000000000 : ℝ) = (278330392119 / 200000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (278330392119 / 200000000000 : ℝ) ≤
            (413114377927187151583 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (519239595879119 / 625000000000000 : ℝ) ≤ Real.sqrt (276080392119 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (276080392119 / 400000000000 : ℝ) ≤ (8307833534065907 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (276080392119 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau966 :
    Real.arctan (488696090239171 / 1352986645774332 : ℝ) ≤
      (69323148149546782071 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau965 :
    Real.arctan (8307833534065907 / 10000000000000000 : ℝ) ≤
      (2 * (69323148149546782071 / 200000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3250193244540911 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8307833534065907 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8307833534065907 / 10000000000000000 : ℝ) /
                (1 + (3250193244540911 / 2500000000000000 : ℝ)) =
              (488696090239171 / 1352986645774332 : ℝ)
            by
        norm_num];
        exact hau966)
  have hat1 :
    (Real.pi / 2 - (2 * (69323148149546782071 / 200000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8307833534065907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8307833534065907 : ℝ) =
              (8307833534065907 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau965)
  have hz1 :
    (10000000000000000 / 8307833534065907 : ℝ) ≤
      1 / Real.sqrt (276080392119 / 400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8307833534065907 : ℝ) =
          1 / (8307833534065907 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 519239595879119 : ℝ) ≤
      (225080477410010679099 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (276080392119 / 400000000000 : ℝ) ≤
      (46875000000000 / 519239595879119 : ℝ) := by
    rw [show
        (46875000000000 / 519239595879119 : ℝ) =
          (3 / 40) / (519239595879119 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (69323148149546782071 / 200000000000000000000 : ℝ))) -
        6 * (225080477410010679099 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (276080392119 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (276080392119 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((519239595879119 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (69323148149546782071 / 200000000000000000000 : ℝ))) -
          6 * (225080477410010679099 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (276080392119 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (276080392119 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (276080392119 / 400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_598 :
    ((656659118777736086491 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3614904945718563204627 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8312714464589487 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3467600951686490417953 / 10000000000000000000000 : ℝ))) -
              6 * (899796122169194200699 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (44224781932669 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (44224781932669 / 64000000000000 : ℝ)) =
      Real.log (108224781932669 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((44224781932669 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (44584781932669 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (656659118777736086491 / 1250000000000000000000 : ℝ) ≤
      Real.log (108224781932669 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (44584781932669 / 64000000000000 : ℝ) ≤
      (-(3614904945718563204627 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44584781932669 / 64000000000000 : ℝ) = (44584781932669 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44584781932669 / 32000000000000 : ℝ) ≤
            (3316566857281436795373 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8312714464589487 / 10000000000000000 : ℝ) ≤
      Real.sqrt (44224781932669 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (44224781932669 / 64000000000000 : ℝ) ≤ (831271446458949 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (44224781932669 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau968 :
    Real.arctan (2770904821529830 / 7667964187407111 : ℝ) ≤
      (3467600951686490417953 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau967 :
    Real.arctan (831271446458949 / 1000000000000000 : ℝ) ≤
      (2 * (3467600951686490417953 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13003892562221333 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (831271446458949 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (831271446458949 / 1000000000000000 : ℝ) /
                (1 + (13003892562221333 / 10000000000000000 : ℝ)) =
              (2770904821529830 / 7667964187407111 : ℝ)
            by
        norm_num];
        exact hau968)
  have hat1 :
    (Real.pi / 2 - (2 * (3467600951686490417953 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 831271446458949 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 831271446458949 : ℝ) =
              (831271446458949 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau967)
  have hz1 :
    (1000000000000000 / 831271446458949 : ℝ) ≤
      1 / Real.sqrt (44224781932669 / 64000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 831271446458949 : ℝ) = 1 / (831271446458949 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2770904821529829 : ℝ) ≤
      (899796122169194200699 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (44224781932669 / 64000000000000 : ℝ) ≤
      (250000000000000 / 2770904821529829 : ℝ) := by
    rw [show
        (250000000000000 / 2770904821529829 : ℝ) =
          (3 / 40) / (8312714464589487 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3467600951686490417953 / 10000000000000000000000 : ℝ))) -
        6 * (899796122169194200699 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (44224781932669 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (44224781932669 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8312714464589487 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3467600951686490417953 / 10000000000000000000000 : ℝ))) -
          6 * (899796122169194200699 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (44224781932669 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (44224781932669 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (44224781932669 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_599 :
    ((5258069147817461612193 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3603266672578664989709 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((41587962654427 / 50000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3469042956848913514917 / 10000000000000000000000 : ℝ))) -
              6 * (899271254807820140911 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22138350563149 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22138350563149 / 32000000000000 : ℝ)) =
      Real.log (54138350563149 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22138350563149 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22318350563149 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5258069147817461612193 / 10000000000000000000000 : ℝ) ≤
      Real.log (54138350563149 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22318350563149 / 32000000000000 : ℝ) ≤
      (-(3603266672578664989709 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22318350563149 / 32000000000000 : ℝ) = (22318350563149 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22318350563149 / 16000000000000 : ℝ) ≤
            (3328205130421335010291 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (41587962654427 / 50000000000000 : ℝ) ≤ Real.sqrt (22138350563149 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22138350563149 / 32000000000000 : ℝ) ≤
      (8317592530885403 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22138350563149 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau970 :
    Real.arctan (8317592530885403 / 23007011398082213 : ℝ) ≤
      (3469042956848913514917 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau969 :
    Real.arctan (8317592530885403 / 10000000000000000 : ℝ) ≤
      (2 * (3469042956848913514917 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13007011398082213 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8317592530885403 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8317592530885403 / 10000000000000000 : ℝ) /
                (1 + (13007011398082213 / 10000000000000000 : ℝ)) =
              (8317592530885403 / 23007011398082213 : ℝ)
            by
        norm_num];
        exact hau970)
  have hat1 :
    (Real.pi / 2 - (2 * (3469042956848913514917 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8317592530885403 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8317592530885403 : ℝ) =
              (8317592530885403 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau969)
  have hz1 :
    (10000000000000000 / 8317592530885403 : ℝ) ≤
      1 / Real.sqrt (22138350563149 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8317592530885403 : ℝ) =
          1 / (8317592530885403 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (3750000000000 / 41587962654427 : ℝ) ≤
      (899271254807820140911 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22138350563149 / 32000000000000 : ℝ) ≤
      (3750000000000 / 41587962654427 : ℝ) := by
    rw [show
        (3750000000000 / 41587962654427 : ℝ) = (3 / 40) / (41587962654427 / 50000000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3469042956848913514917 / 10000000000000000000000 : ℝ))) -
        6 * (899271254807820140911 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22138350563149 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22138350563149 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((41587962654427 / 50000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3469042956848913514917 / 10000000000000000000000 : ℝ))) -
          6 * (899271254807820140911 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22138350563149 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22138350563149 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22138350563149 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_600 :
    ((131571576154115446801 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(897910482158703023617 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2080616934497523 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3470483425928326162743 / 10000000000000000000000 : ℝ))) -
              6 * (898747304875433424139 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (44328620319927 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (44328620319927 / 64000000000000 : ℝ)) =
      Real.log (108328620319927 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((44328620319927 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (44688620319927 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (131571576154115446801 / 250000000000000000000 : ℝ) ≤
      Real.log (108328620319927 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (44688620319927 / 64000000000000 : ℝ) ≤
      (-(897910482158703023617 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44688620319927 / 64000000000000 : ℝ) = (44688620319927 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44688620319927 / 32000000000000 : ℝ) ≤
            (834957468591296976383 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2080616934497523 / 2500000000000000 : ℝ) ≤ Real.sqrt (44328620319927 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (44328620319927 / 64000000000000 : ℝ) ≤ (1664493547598019 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (44328620319927 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau972 :
    Real.arctan (2774155912663365 / 7670043162094789 : ℝ) ≤
      (3470483425928326162743 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau971 :
    Real.arctan (1664493547598019 / 2000000000000000 : ℝ) ≤
      (2 * (3470483425928326162743 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13010129486284367 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1664493547598019 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1664493547598019 / 2000000000000000 : ℝ) /
                (1 + (13010129486284367 / 10000000000000000 : ℝ)) =
              (2774155912663365 / 7670043162094789 : ℝ)
            by
        norm_num];
        exact hau972)
  have hat1 :
    (Real.pi / 2 - (2 * (3470483425928326162743 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1664493547598019 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1664493547598019 : ℝ) =
              (1664493547598019 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau971)
  have hz1 :
    (2000000000000000 / 1664493547598019 : ℝ) ≤
      1 / Real.sqrt (44328620319927 / 64000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1664493547598019 : ℝ) = 1 / (1664493547598019 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 693538978165841 : ℝ) ≤
      (898747304875433424139 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (44328620319927 / 64000000000000 : ℝ) ≤
      (62500000000000 / 693538978165841 : ℝ) := by
    rw [show
        (62500000000000 / 693538978165841 : ℝ) =
          (3 / 40) / (2080616934497523 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3470483425928326162743 / 10000000000000000000000 : ℝ))) -
        6 * (898747304875433424139 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (44328620319927 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (44328620319927 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2080616934497523 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3470483425928326162743 / 10000000000000000000000 : ℝ))) -
          6 * (898747304875433424139 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (44328620319927 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (44328620319927 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (44328620319927 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
