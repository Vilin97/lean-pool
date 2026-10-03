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

/-! # V11: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_133 :
    ((190058421104230496931 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6174174657182944863893 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2810476616623781 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2739799349363924849661 / 10000000000000000000000 : ℝ)) -
              6 * (2607816221361664600063 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5055218440057 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5055218440057 / 64000000000000 : ℝ)) =
      Real.log (69055218440057 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5055218440057 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5415218440057 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (190058421104230496931 / 2500000000000000000000 : ℝ) ≤
      Real.log (69055218440057 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5415218440057 / 64000000000000 : ℝ) ≤
      (-(6174174657182944863893 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5415218440057 / 64000000000000 : ℝ) = (5415218440057 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5415218440057 / 4000000000000 : ℝ) ≤
            (757297145817055136107 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2810476616623781 / 10000000000000000 : ℝ) ≤ Real.sqrt (5055218440057 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5055218440057 / 64000000000000 : ℝ) ≤ (351309577077973 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5055218440057 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau195 :
    Real.arctan (351309577077973 / 1250000000000000 : ℝ) ≤
      (2739799349363924849661 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2739799349363924849661 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 351309577077973 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 351309577077973 : ℝ) =
              (351309577077973 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau195)
  have hz1 :
    (1250000000000000 / 351309577077973 : ℝ) ≤
      1 / Real.sqrt (5055218440057 / 64000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 351309577077973 : ℝ) = 1 / (351309577077973 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2810476616623781 : ℝ) ≤
      (2607816221361664600063 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5055218440057 / 64000000000000 : ℝ) ≤
      (750000000000000 / 2810476616623781 : ℝ) := by
    rw [show
        (750000000000000 / 2810476616623781 : ℝ) =
          (3 / 40) / (2810476616623781 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2739799349363924849661 / 10000000000000000000000 : ℝ)) -
        6 * (2607816221361664600063 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5055218440057 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5055218440057 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2810476616623781 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2739799349363924849661 / 10000000000000000000000 : ℝ)) -
          6 * (2607816221361664600063 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5055218440057 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5055218440057 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5055218440057 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_134 :
    ((382551253599223766289 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1231739400428765560097 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((140990474916221 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (687111727224121272759 / 2500000000000000000000 : ℝ)) -
              6 * (1299784604025157638269 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2544424194189 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2544424194189 / 32000000000000 : ℝ)) =
      Real.log (34544424194189 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2544424194189 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2724424194189 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (382551253599223766289 / 5000000000000000000000 : ℝ) ≤
      Real.log (34544424194189 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2724424194189 / 32000000000000 : ℝ) ≤
      (-(1231739400428765560097 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2724424194189 / 32000000000000 : ℝ) = (2724424194189 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2724424194189 / 2000000000000 : ℝ) ≤
            (154554960171234439903 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (140990474916221 / 500000000000000 : ℝ) ≤ Real.sqrt (2544424194189 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2544424194189 / 32000000000000 : ℝ) ≤ (2819809498324423 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2544424194189 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau196 :
    Real.arctan (2819809498324423 / 10000000000000000 : ℝ) ≤
      (687111727224121272759 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (687111727224121272759 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2819809498324423 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2819809498324423 : ℝ) =
              (2819809498324423 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau196)
  have hz1 :
    (10000000000000000 / 2819809498324423 : ℝ) ≤
      1 / Real.sqrt (2544424194189 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2819809498324423 : ℝ) =
          1 / (2819809498324423 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (37500000000000 / 140990474916221 : ℝ) ≤
      (1299784604025157638269 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2544424194189 / 32000000000000 : ℝ) ≤
      (37500000000000 / 140990474916221 : ℝ) := by
    rw [show
        (37500000000000 / 140990474916221 : ℝ) =
          (3 / 40) / (140990474916221 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (687111727224121272759 / 2500000000000000000000 : ℝ)) -
        6 * (1299784604025157638269 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2544424194189 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2544424194189 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((140990474916221 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (687111727224121272759 / 2500000000000000000000 : ℝ)) -
          6 * (1299784604025157638269 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (2544424194189 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2544424194189 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2544424194189 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_135 :
    ((30798758423600499343 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4914651664744565192507 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2829111592195009 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (689265436739419728229 / 2500000000000000000000 : ℝ)) -
              6 * (1295699988500512258437 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (5122478336699 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5122478336699 / 64000000000000 : ℝ)) =
      Real.log (69122478336699 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5122478336699 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5482478336699 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (30798758423600499343 / 400000000000000000000 : ℝ) ≤
      Real.log (69122478336699 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5482478336699 / 64000000000000 : ℝ) ≤
      (-(4914651664744565192507 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5482478336699 / 64000000000000 : ℝ) = (5482478336699 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5482478336699 / 4000000000000 : ℝ) ≤
            (630525777655434807493 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2829111592195009 / 10000000000000000 : ℝ) ≤ Real.sqrt (5122478336699 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5122478336699 / 64000000000000 : ℝ) ≤ (707277898048753 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5122478336699 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau197 :
    Real.arctan (707277898048753 / 2500000000000000 : ℝ) ≤
      (689265436739419728229 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (689265436739419728229 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 707277898048753 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 707277898048753 : ℝ) =
              (707277898048753 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau197)
  have hz1 :
    (2500000000000000 / 707277898048753 : ℝ) ≤
      1 / Real.sqrt (5122478336699 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 707277898048753 : ℝ) = 1 / (707277898048753 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2829111592195009 : ℝ) ≤
      (1295699988500512258437 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5122478336699 / 64000000000000 : ℝ) ≤
      (750000000000000 / 2829111592195009 : ℝ) := by
    rw [show
        (750000000000000 / 2829111592195009 : ℝ) =
          (3 / 40) / (2829111592195009 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (689265436739419728229 / 2500000000000000000000 : ℝ)) -
        6 * (1295699988500512258437 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5122478336699 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5122478336699 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2829111592195009 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (689265436739419728229 / 2500000000000000000000 : ℝ)) -
          6 * (1295699988500512258437 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (5122478336699 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5122478336699 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5122478336699 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_136 :
    ((774833046896600384011 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24512104915046550125607 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((567676640186779 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (691411043894439901673 / 2500000000000000000000 : ℝ)) -
              6 * (645826828166487246769 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (257805414251 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (257805414251 / 3200000000000 : ℝ)) =
      Real.log (3457805414251 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((257805414251 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (275805414251 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (774833046896600384011 / 10000000000000000000000 : ℝ) ≤
      Real.log (3457805414251 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (275805414251 / 3200000000000 : ℝ) ≤
      (-(24512104915046550125607 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (275805414251 / 3200000000000 : ℝ) = (275805414251 / 200000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (275805414251 / 200000000000 : ℝ) ≤
            (3213782296953449874393 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (567676640186779 / 2000000000000000 : ℝ) ≤ Real.sqrt (257805414251 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (257805414251 / 3200000000000 : ℝ) ≤ (1419191600466949 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (257805414251 / 3200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau198 :
    Real.arctan (1419191600466949 / 5000000000000000 : ℝ) ≤
      (691411043894439901673 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (691411043894439901673 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1419191600466949 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1419191600466949 : ℝ) =
              (1419191600466949 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau198)
  have hz1 :
    (5000000000000000 / 1419191600466949 : ℝ) ≤
      1 / Real.sqrt (257805414251 / 3200000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1419191600466949 : ℝ) = 1 / (1419191600466949 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 567676640186779 : ℝ) ≤
      (645826828166487246769 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (257805414251 / 3200000000000 : ℝ) ≤
      (150000000000000 / 567676640186779 : ℝ) := by
    rw [show
        (150000000000000 / 567676640186779 : ℝ) =
          (3 / 40) / (567676640186779 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (691411043894439901673 / 2500000000000000000000 : ℝ)) -
        6 * (645826828166487246769 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (257805414251 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (257805414251 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((567676640186779 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (691411043894439901673 / 2500000000000000000000 : ℝ)) -
          6 * (645826828166487246769 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (257805414251 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (257805414251 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (257805414251 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_137 :
    ((196138531864494114447 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3048863589055876755923 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2856836149282431 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2782713027656475583597 / 10000000000000000000000 : ℝ)) -
              6 * (2567346953413312793429 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2611684090831 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2611684090831 / 32000000000000 : ℝ)) =
      Real.log (34611684090831 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2611684090831 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2791684090831 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (196138531864494114447 / 2500000000000000000000 : ℝ) ≤
      Real.log (34611684090831 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2791684090831 / 32000000000000 : ℝ) ≤
      (-(3048863589055876755923 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2791684090831 / 32000000000000 : ℝ) = (2791684090831 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2791684090831 / 2000000000000 : ℝ) ≤
            (416872312444123244077 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2856836149282431 / 10000000000000000 : ℝ) ≤ Real.sqrt (2611684090831 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2611684090831 / 32000000000000 : ℝ) ≤ (1428418074641217 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2611684090831 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau199 :
    Real.arctan (1428418074641217 / 5000000000000000 : ℝ) ≤
      (2782713027656475583597 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2782713027656475583597 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1428418074641217 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1428418074641217 : ℝ) =
              (1428418074641217 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau199)
  have hz1 :
    (5000000000000000 / 1428418074641217 : ℝ) ≤
      1 / Real.sqrt (2611684090831 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1428418074641217 : ℝ) = 1 / (1428418074641217 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 952278716427477 : ℝ) ≤
      (2567346953413312793429 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2611684090831 / 32000000000000 : ℝ) ≤
      (250000000000000 / 952278716427477 : ℝ) := by
    rw [show
        (250000000000000 / 952278716427477 : ℝ) =
          (3 / 40) / (2856836149282431 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2782713027656475583597 / 10000000000000000000000 : ℝ)) -
        6 * (2567346953413312793429 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2611684090831 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2611684090831 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2856836149282431 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2782713027656475583597 / 10000000000000000000000 : ℝ)) -
          6 * (2567346953413312793429 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2611684090831 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2611684090831 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2611684090831 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_138 :
    ((198566441813831119773 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3033895473797801538299 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1437585334193243 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (279965586309664145921 / 1000000000000000000000 : ℝ)) -
              6 * (2551678921654980299883 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (165332127447 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (165332127447 / 2000000000000 : ℝ)) =
      Real.log (2165332127447 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((165332127447 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (176582127447 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (198566441813831119773 / 2500000000000000000000 : ℝ) ≤
      Real.log (2165332127447 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (176582127447 / 2000000000000 : ℝ) ≤
      (-(3033895473797801538299 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (176582127447 / 2000000000000 : ℝ) = (176582127447 / 125000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (176582127447 / 125000000000 : ℝ) ≤
            (431840427702198461701 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1437585334193243 / 5000000000000000 : ℝ) ≤ Real.sqrt (165332127447 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (165332127447 / 2000000000000 : ℝ) ≤ (2875170668386489 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (165332127447 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau200 :
    Real.arctan (2875170668386489 / 10000000000000000 : ℝ) ≤
      (279965586309664145921 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (279965586309664145921 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2875170668386489 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2875170668386489 : ℝ) =
              (2875170668386489 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau200)
  have hz1 :
    (10000000000000000 / 2875170668386489 : ℝ) ≤
      1 / Real.sqrt (165332127447 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2875170668386489 : ℝ) =
          1 / (2875170668386489 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1437585334193243 : ℝ) ≤
      (2551678921654980299883 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (165332127447 / 2000000000000 : ℝ) ≤
      (375000000000000 / 1437585334193243 : ℝ) := by
    rw [show
        (375000000000000 / 1437585334193243 : ℝ) =
          (3 / 40) / (1437585334193243 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (279965586309664145921 / 1000000000000000000000 : ℝ)) -
        6 * (2551678921654980299883 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (165332127447 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (165332127447 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1437585334193243 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (279965586309664145921 / 1000000000000000000000 : ℝ)) -
          6 * (2551678921654980299883 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (165332127447 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (165332127447 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (165332127447 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_139 :
    ((803967984607916239937 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1207641790130783507417 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2893389009596379 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2816475004873911548537 / 10000000000000000000000 : ℝ)) -
              6 * (1268147198934660719937 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2678943987473 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2678943987473 / 32000000000000 : ℝ)) =
      Real.log (34678943987473 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2678943987473 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2858943987473 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (803967984607916239937 / 10000000000000000000000 : ℝ) ≤
      Real.log (34678943987473 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2858943987473 / 32000000000000 : ℝ) ≤
      (-(1207641790130783507417 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2858943987473 / 32000000000000 : ℝ) = (2858943987473 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2858943987473 / 2000000000000 : ℝ) ≤
            (178652570469216492583 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2893389009596379 / 10000000000000000 : ℝ) ≤ Real.sqrt (2678943987473 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2678943987473 / 32000000000000 : ℝ) ≤ (1446694504798191 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2678943987473 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau201 :
    Real.arctan (1446694504798191 / 5000000000000000 : ℝ) ≤
      (2816475004873911548537 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2816475004873911548537 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1446694504798191 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1446694504798191 : ℝ) =
              (1446694504798191 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau201)
  have hz1 :
    (5000000000000000 / 1446694504798191 : ℝ) ≤
      1 / Real.sqrt (2678943987473 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1446694504798191 : ℝ) = 1 / (1446694504798191 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 964463003198793 : ℝ) ≤
      (1268147198934660719937 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2678943987473 / 32000000000000 : ℝ) ≤
      (250000000000000 / 964463003198793 : ℝ) := by
    rw [show
        (250000000000000 / 964463003198793 : ℝ) =
          (3 / 40) / (2893389009596379 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2816475004873911548537 / 10000000000000000000000 : ℝ)) -
        6 * (1268147198934660719937 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2678943987473 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2678943987473 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2893389009596379 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2816475004873911548537 / 10000000000000000000000 : ℝ)) -
          6 * (1268147198934660719937 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (2678943987473 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2678943987473 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2678943987473 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_140 :
    ((406830398890876967997 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24035891607929812287671 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2911493353823127 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1416586352121228549643 / 5000000000000000000000 : ℝ)) -
              6 * (1260592465377202839901 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1356286967897 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1356286967897 / 16000000000000 : ℝ)) =
      Real.log (17356286967897 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1356286967897 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1446286967897 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (406830398890876967997 / 5000000000000000000000 : ℝ) ≤
      Real.log (17356286967897 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1446286967897 / 16000000000000 : ℝ) ≤
      (-(24035891607929812287671 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1446286967897 / 16000000000000 : ℝ) = (1446286967897 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1446286967897 / 1000000000000 : ℝ) ≤
            (3689995604070187712329 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2911493353823127 / 10000000000000000 : ℝ) ≤ Real.sqrt (1356286967897 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1356286967897 / 16000000000000 : ℝ) ≤ (291149335382313 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1356286967897 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau202 :
    Real.arctan (291149335382313 / 1000000000000000 : ℝ) ≤
      (1416586352121228549643 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1416586352121228549643 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 291149335382313 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 291149335382313 : ℝ) =
              (291149335382313 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau202)
  have hz1 :
    (1000000000000000 / 291149335382313 : ℝ) ≤
      1 / Real.sqrt (1356286967897 / 16000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 291149335382313 : ℝ) = 1 / (291149335382313 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 970497784607709 : ℝ) ≤
      (1260592465377202839901 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1356286967897 / 16000000000000 : ℝ) ≤
      (250000000000000 / 970497784607709 : ℝ) := by
    rw [show
        (250000000000000 / 970497784607709 : ℝ) =
          (3 / 40) / (2911493353823127 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1416586352121228549643 / 5000000000000000000000 : ℝ)) -
        6 * (1260592465377202839901 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1356286967897 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1356286967897 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2911493353823127 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1416586352121228549643 / 5000000000000000000000 : ℝ)) -
          6 * (1260592465377202839901 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1356286967897 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1356286967897 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1356286967897 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_141 :
    ((52063642774504058401 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2380602772690295968647 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2947368440891381 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1433106220253817106089 / 5000000000000000000000 : ℝ)) -
              6 * (1245879543219645552791 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (694958458109 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (694958458109 / 8000000000000 : ℝ)) =
      Real.log (8694958458109 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((694958458109 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (739958458109 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (52063642774504058401 / 625000000000000000000 : ℝ) ≤
      Real.log (8694958458109 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (739958458109 / 8000000000000 : ℝ) ≤
      (-(2380602772690295968647 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (739958458109 / 8000000000000 : ℝ) = (739958458109 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (739958458109 / 500000000000 : ℝ) ≤
            (391985948509704031353 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2947368440891381 / 10000000000000000 : ℝ) ≤ Real.sqrt (694958458109 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (694958458109 / 8000000000000 : ℝ) ≤ (368421055111423 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (694958458109 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau203 :
    Real.arctan (368421055111423 / 1250000000000000 : ℝ) ≤
      (1433106220253817106089 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1433106220253817106089 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 368421055111423 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 368421055111423 : ℝ) =
              (368421055111423 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau203)
  have hz1 :
    (1250000000000000 / 368421055111423 : ℝ) ≤ 1 / Real.sqrt (694958458109 / 8000000000000 : ℝ) :=
  by
    rw [show
        (1250000000000000 / 368421055111423 : ℝ) = 1 / (368421055111423 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2947368440891381 : ℝ) ≤
      (1245879543219645552791 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (694958458109 / 8000000000000 : ℝ) ≤
      (750000000000000 / 2947368440891381 : ℝ) := by
    rw [show
        (750000000000000 / 2947368440891381 : ℝ) =
          (3 / 40) / (2947368440891381 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1433106220253817106089 / 5000000000000000000000 : ℝ)) -
        6 * (1245879543219645552791 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (694958458109 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (694958458109 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2947368440891381 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1433106220253817106089 / 5000000000000000000000 : ℝ)) -
          6 * (1245879543219645552791 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (694958458109 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (694958458109 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (694958458109 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_142 :
    ((852338372156698860517 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(23581329078528711081391 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1491406039897313 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2898791760613854838001 / 10000000000000000000000 : ℝ)) -
              6 * (2463340430743041968497 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1423546864539 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1423546864539 / 16000000000000 : ℝ)) =
      Real.log (17423546864539 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1423546864539 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1513546864539 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (852338372156698860517 / 10000000000000000000000 : ℝ) ≤
      Real.log (17423546864539 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1513546864539 / 16000000000000 : ℝ) ≤
      (-(23581329078528711081391 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1513546864539 / 16000000000000 : ℝ) = (1513546864539 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1513546864539 / 1000000000000 : ℝ) ≤
            (4144558133471288918609 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1491406039897313 / 5000000000000000 : ℝ) ≤ Real.sqrt (1423546864539 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1423546864539 / 16000000000000 : ℝ) ≤ (2982812079794629 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1423546864539 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau204 :
    Real.arctan (2982812079794629 / 10000000000000000 : ℝ) ≤
      (2898791760613854838001 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2898791760613854838001 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2982812079794629 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2982812079794629 : ℝ) =
              (2982812079794629 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau204)
  have hz1 :
    (10000000000000000 / 2982812079794629 : ℝ) ≤
      1 / Real.sqrt (1423546864539 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2982812079794629 : ℝ) =
          1 / (2982812079794629 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1491406039897313 : ℝ) ≤
      (2463340430743041968497 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1423546864539 / 16000000000000 : ℝ) ≤
      (375000000000000 / 1491406039897313 : ℝ) := by
    rw [show
        (375000000000000 / 1491406039897313 : ℝ) =
          (3 / 40) / (1491406039897313 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2898791760613854838001 / 10000000000000000000000 : ℝ)) -
        6 * (2463340430743041968497 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1423546864539 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1423546864539 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1491406039897313 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2898791760613854838001 / 10000000000000000000000 : ℝ)) -
          6 * (2463340430743041968497 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1423546864539 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1423546864539 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1423546864539 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_143 :
    ((43581060265344278991 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(23361568621129862900791 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3017839472267369 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1465463193295560484297 / 5000000000000000000000 : ℝ)) -
              6 * (487174553803326026091 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (72858840643 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (72858840643 / 800000000000 : ℝ)) =
      Real.log (872858840643 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((72858840643 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (77358840643 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (43581060265344278991 / 500000000000000000000 : ℝ) ≤
      Real.log (872858840643 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (77358840643 / 800000000000 : ℝ) ≤
      (-(23361568621129862900791 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (77358840643 / 800000000000 : ℝ) = (77358840643 / 50000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (77358840643 / 50000000000 : ℝ) ≤
            (4364318590870137099209 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3017839472267369 / 10000000000000000 : ℝ) ≤ Real.sqrt (72858840643 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (72858840643 / 800000000000 : ℝ) ≤ (754459868066843 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (72858840643 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau205 :
    Real.arctan (754459868066843 / 2500000000000000 : ℝ) ≤
      (1465463193295560484297 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1465463193295560484297 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 754459868066843 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 754459868066843 : ℝ) =
              (754459868066843 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau205)
  have hz1 :
    (2500000000000000 / 754459868066843 : ℝ) ≤ 1 / Real.sqrt (72858840643 / 800000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 754459868066843 : ℝ) = 1 / (754459868066843 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3017839472267369 : ℝ) ≤
      (487174553803326026091 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (72858840643 / 800000000000 : ℝ) ≤
      (750000000000000 / 3017839472267369 : ℝ) := by
    rw [show
        (750000000000000 / 3017839472267369 : ℝ) =
          (3 / 40) / (3017839472267369 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1465463193295560484297 / 5000000000000000000000 : ℝ)) -
        6 * (487174553803326026091 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (72858840643 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (72858840643 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3017839472267369 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1465463193295560484297 / 5000000000000000000000 : ℝ)) -
          6 * (487174553803326026091 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (72858840643 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (72858840643 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (72858840643 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_144 :
    ((910075680531480208983 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(22936026120516716875781 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1543351016002799 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (18712000414536656493 / 62500000000000000000 : ℝ)) -
              6 * (595896677737549471971 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (762218354751 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (762218354751 / 8000000000000 : ℝ)) =
      Real.log (8762218354751 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((762218354751 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (807218354751 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (910075680531480208983 / 10000000000000000000000 : ℝ) ≤
      Real.log (8762218354751 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (807218354751 / 8000000000000 : ℝ) ≤
      (-(22936026120516716875781 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (807218354751 / 8000000000000 : ℝ) = (807218354751 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (807218354751 / 500000000000 : ℝ) ≤
            (4789861091483283124219 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1543351016002799 / 5000000000000000 : ℝ) ≤ Real.sqrt (762218354751 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (762218354751 / 8000000000000 : ℝ) ≤ (3086702032005601 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (762218354751 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau206 :
    Real.arctan (3086702032005601 / 10000000000000000 : ℝ) ≤
      (18712000414536656493 / 62500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (18712000414536656493 / 62500000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3086702032005601 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3086702032005601 : ℝ) =
              (3086702032005601 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau206)
  have hz1 :
    (10000000000000000 / 3086702032005601 : ℝ) ≤
      1 / Real.sqrt (762218354751 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3086702032005601 : ℝ) =
          1 / (3086702032005601 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1543351016002799 : ℝ) ≤
      (595896677737549471971 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (762218354751 / 8000000000000 : ℝ) ≤
      (375000000000000 / 1543351016002799 : ℝ) := by
    rw [show
        (375000000000000 / 1543351016002799 : ℝ) =
          (3 / 40) / (1543351016002799 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (18712000414536656493 / 62500000000000000000 : ℝ)) -
        6 * (595896677737549471971 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (762218354751 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (762218354751 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1543351016002799 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (18712000414536656493 / 62500000000000000000 : ℝ)) -
          6 * (595896677737549471971 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (762218354751 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (762218354751 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (762218354751 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
