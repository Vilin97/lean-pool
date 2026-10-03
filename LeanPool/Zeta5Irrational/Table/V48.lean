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

/-! # V48: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_577 :
    ((5152017738114334704557 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3862490756705591713337 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8209605546482957 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1718479340793304782101 / 5000000000000000000000 : ℝ))) -
              6 * (911035109185732816891 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2156723943323 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2156723943323 / 3200000000000 : ℝ)) =
      Real.log (5356723943323 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2156723943323 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2174723943323 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5152017738114334704557 / 10000000000000000000000 : ℝ) ≤
      Real.log (5356723943323 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2174723943323 / 3200000000000 : ℝ) ≤
      (-(3862490756705591713337 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2174723943323 / 3200000000000 : ℝ) = (2174723943323 / 1600000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2174723943323 / 1600000000000 : ℝ) ≤
            (3068981046294408286663 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8209605546482957 / 10000000000000000 : ℝ) ≤ Real.sqrt (2156723943323 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2156723943323 / 3200000000000 : ℝ) ≤ (102620069331037 / 125000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2156723943323 / 3200000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau926 :
    Real.arctan (2052401386620740 / 5734555835320011 : ℝ) ≤
      (1718479340793304782101 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau925 :
    Real.arctan (102620069331037 / 125000000000000 : ℝ) ≤
      (2 * (1718479340793304782101 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3234555835320011 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (102620069331037 / 125000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (102620069331037 / 125000000000000 : ℝ) /
                (1 + (3234555835320011 / 2500000000000000 : ℝ)) =
              (2052401386620740 / 5734555835320011 : ℝ)
            by
        norm_num];
        exact hau926)
  have hat1 :
    (Real.pi / 2 - (2 * (1718479340793304782101 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (125000000000000 / 102620069331037 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 102620069331037 : ℝ) =
              (102620069331037 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hau925)
  have hz1 :
    (125000000000000 / 102620069331037 : ℝ) ≤ 1 / Real.sqrt (2156723943323 / 3200000000000 : ℝ) :=
  by
    rw [show (125000000000000 / 102620069331037 : ℝ) = 1 / (102620069331037 / 125000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8209605546482957 : ℝ) ≤
      (911035109185732816891 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2156723943323 / 3200000000000 : ℝ) ≤
      (750000000000000 / 8209605546482957 : ℝ) := by
    rw [show
        (750000000000000 / 8209605546482957 : ℝ) =
          (3 / 40) / (8209605546482957 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1718479340793304782101 / 5000000000000000000000 : ℝ))) -
        6 * (911035109185732816891 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2156723943323 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2156723943323 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8209605546482957 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1718479340793304782101 / 5000000000000000000000 : ℝ))) -
          6 * (911035109185732816891 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2156723943323 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2156723943323 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2156723943323 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_578 :
    ((1031372546917553828993 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3850560913712286605501 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((410727242123313 / 500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3438433642688509428973 / 10000000000000000000000 : ℝ))) -
              6 * (9104903392848186487 / 100000000000000000000 : ℝ)))) ≤
      Vfield (43186398060089 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43186398060089 / 64000000000000 : ℝ)) =
      Real.log (107186398060089 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43186398060089 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (43546398060089 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1031372546917553828993 / 2000000000000000000000 : ℝ) ≤
      Real.log (107186398060089 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (43546398060089 / 64000000000000 : ℝ) ≤
      (-(3850560913712286605501 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43546398060089 / 64000000000000 : ℝ) = (43546398060089 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43546398060089 / 32000000000000 : ℝ) ≤
            (3080910889287713394499 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (410727242123313 / 500000000000000 : ℝ) ≤ Real.sqrt (43186398060089 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43186398060089 / 64000000000000 : ℝ) ≤
      (8214544842466263 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43186398060089 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau928 :
    Real.arctan (2738181614155421 / 7647119334424474 : ℝ) ≤
      (3438433642688509428973 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau927 :
    Real.arctan (8214544842466263 / 10000000000000000 : ℝ) ≤
      (2 * (3438433642688509428973 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6470679001636711 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8214544842466263 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8214544842466263 / 10000000000000000 : ℝ) /
                (1 + (6470679001636711 / 5000000000000000 : ℝ)) =
              (2738181614155421 / 7647119334424474 : ℝ)
            by
        norm_num];
        exact hau928)
  have hat1 :
    (Real.pi / 2 - (2 * (3438433642688509428973 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8214544842466263 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8214544842466263 : ℝ) =
              (8214544842466263 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau927)
  have hz1 :
    (10000000000000000 / 8214544842466263 : ℝ) ≤
      1 / Real.sqrt (43186398060089 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8214544842466263 : ℝ) =
          1 / (8214544842466263 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (12500000000000 / 136909080707771 : ℝ) ≤
      (9104903392848186487 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43186398060089 / 64000000000000 : ℝ) ≤
      (12500000000000 / 136909080707771 : ℝ) := by
    rw [show
        (12500000000000 / 136909080707771 : ℝ) =
          (3 / 40) / (410727242123313 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3438433642688509428973 / 10000000000000000000000 : ℝ))) -
        6 * (9104903392848186487 / 100000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43186398060089 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43186398060089 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((410727242123313 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3438433642688509428973 / 10000000000000000000000 : ℝ))) -
          6 * (9104903392848186487 / 100000000000000000000 : ℝ))) ≤
      Real.sqrt (43186398060089 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43186398060089 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43186398060089 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_579 :
    ((5161705384798838239711 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(959661321469397220031 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8219481170301101 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1719953501802942922099 / 5000000000000000000000 : ℝ))) -
              6 * (227486636371899300713 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (21619158626859 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21619158626859 / 32000000000000 : ℝ)) =
      Real.log (53619158626859 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21619158626859 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21799158626859 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5161705384798838239711 / 10000000000000000000000 : ℝ) ≤
      Real.log (53619158626859 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21799158626859 / 32000000000000 : ℝ) ≤
      (-(959661321469397220031 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21799158626859 / 32000000000000 : ℝ) = (21799158626859 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21799158626859 / 16000000000000 : ℝ) ≤
            (773206629280602779969 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8219481170301101 / 10000000000000000 : ℝ) ≤
      Real.sqrt (21619158626859 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21619158626859 / 32000000000000 : ℝ) ≤ (513717573143819 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21619158626859 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau930 :
    Real.arctan (8219481170301104 / 22944491906171303 : ℝ) ≤
      (1719953501802942922099 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau929 :
    Real.arctan (513717573143819 / 625000000000000 : ℝ) ≤
      (2 * (1719953501802942922099 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12944491906171303 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (513717573143819 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (513717573143819 / 625000000000000 : ℝ) /
                (1 + (12944491906171303 / 10000000000000000 : ℝ)) =
              (8219481170301104 / 22944491906171303 : ℝ)
            by
        norm_num];
        exact hau930)
  have hat1 :
    (Real.pi / 2 - (2 * (1719953501802942922099 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 513717573143819 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 513717573143819 : ℝ) =
              (513717573143819 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau929)
  have hz1 :
    (625000000000000 / 513717573143819 : ℝ) ≤
      1 / Real.sqrt (21619158626859 / 32000000000000 : ℝ) := by
    rw [show (625000000000000 / 513717573143819 : ℝ) = 1 / (513717573143819 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8219481170301101 : ℝ) ≤
      (227486636371899300713 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21619158626859 / 32000000000000 : ℝ) ≤
      (750000000000000 / 8219481170301101 : ℝ) := by
    rw [show
        (750000000000000 / 8219481170301101 : ℝ) =
          (3 / 40) / (8219481170301101 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1719953501802942922099 / 5000000000000000000000 : ℝ))) -
        6 * (227486636371899300713 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21619158626859 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21619158626859 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8219481170301101 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1719953501802942922099 / 5000000000000000000000 : ℝ))) -
          6 * (227486636371899300713 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (21619158626859 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21619158626859 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21619158626859 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_580 :
    ((5166545691018867741703 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1913371919682650284589 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8224414535331963 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (860344691870556942057 / 2500000000000000000000 : ℝ))) -
              6 * (454701862441301176601 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (43290236447347 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43290236447347 / 64000000000000 : ℝ)) =
      Real.log (107290236447347 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43290236447347 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (43650236447347 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5166545691018867741703 / 10000000000000000000000 : ℝ) ≤
      Real.log (107290236447347 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (43650236447347 / 64000000000000 : ℝ) ≤
      (-(1913371919682650284589 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43650236447347 / 64000000000000 : ℝ) = (43650236447347 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43650236447347 / 32000000000000 : ℝ) ≤
            (1552363981817349715411 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8224414535331963 / 10000000000000000 : ℝ) ≤
      Real.sqrt (43290236447347 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43290236447347 / 64000000000000 : ℝ) ≤ (4112207267665983 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43290236447347 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau932 :
    Real.arctan (8224414535331966 / 22947625050524891 : ℝ) ≤
      (860344691870556942057 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau931 :
    Real.arctan (4112207267665983 / 5000000000000000 : ℝ) ≤
      (2 * (860344691870556942057 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12947625050524891 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4112207267665983 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4112207267665983 / 5000000000000000 : ℝ) /
                (1 + (12947625050524891 / 10000000000000000 : ℝ)) =
              (8224414535331966 / 22947625050524891 : ℝ)
            by
        norm_num];
        exact hau932)
  have hat1 :
    (Real.pi / 2 - (2 * (860344691870556942057 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4112207267665983 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4112207267665983 : ℝ) =
              (4112207267665983 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau931)
  have hz1 :
    (5000000000000000 / 4112207267665983 : ℝ) ≤
      1 / Real.sqrt (43290236447347 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4112207267665983 : ℝ) = 1 / (4112207267665983 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2741471511777321 : ℝ) ≤
      (454701862441301176601 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43290236447347 / 64000000000000 : ℝ) ≤
      (250000000000000 / 2741471511777321 : ℝ) := by
    rw [show
        (250000000000000 / 2741471511777321 : ℝ) =
          (3 / 40) / (8224414535331963 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (860344691870556942057 / 2500000000000000000000 : ℝ))) -
        6 * (454701862441301176601 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43290236447347 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43290236447347 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8224414535331963 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (860344691870556942057 / 2500000000000000000000 : ℝ))) -
          6 * (454701862441301176601 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (43290236447347 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43290236447347 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43290236447347 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_581 :
    ((2585691827757943412823 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1907428270229945023543 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((514334058930457 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (860712234362921461299 / 2500000000000000000000 : ℝ))) -
              6 * (908861874570511082349 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2708884727561 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2708884727561 / 4000000000000 : ℝ)) =
      Real.log (6708884727561 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2708884727561 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2731384727561 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2585691827757943412823 / 5000000000000000000000 : ℝ) ≤
      Real.log (6708884727561 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2731384727561 / 4000000000000 : ℝ) ≤
      (-(1907428270229945023543 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2731384727561 / 4000000000000 : ℝ) = (2731384727561 / 2000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2731384727561 / 2000000000000 : ℝ) ≤
            (1558307631270054976457 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (514334058930457 / 625000000000000 : ℝ) ≤ Real.sqrt (2708884727561 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2708884727561 / 4000000000000 : ℝ) ≤ (1645868988577463 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2708884727561 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau934 :
    Real.arctan (8229344942887315 / 22950757436884724 : ℝ) ≤
      (860712234362921461299 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau933 :
    Real.arctan (1645868988577463 / 2000000000000000 : ℝ) ≤
      (2 * (860712234362921461299 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3237689359221181 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1645868988577463 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1645868988577463 / 2000000000000000 : ℝ) /
                (1 + (3237689359221181 / 2500000000000000 : ℝ)) =
              (8229344942887315 / 22950757436884724 : ℝ)
            by
        norm_num];
        exact hau934)
  have hat1 :
    (Real.pi / 2 - (2 * (860712234362921461299 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1645868988577463 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1645868988577463 : ℝ) =
              (1645868988577463 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau933)
  have hz1 :
    (2000000000000000 / 1645868988577463 : ℝ) ≤
      1 / Real.sqrt (2708884727561 / 4000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1645868988577463 : ℝ) = 1 / (1645868988577463 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 514334058930457 : ℝ) ≤
      (908861874570511082349 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2708884727561 / 4000000000000 : ℝ) ≤
      (46875000000000 / 514334058930457 : ℝ) := by
    rw [show
        (46875000000000 / 514334058930457 : ℝ) =
          (3 / 40) / (514334058930457 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (860712234362921461299 / 2500000000000000000000 : ℝ))) -
        6 * (908861874570511082349 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2708884727561 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2708884727561 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((514334058930457 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (860712234362921461299 / 2500000000000000000000 : ℝ))) -
          6 * (908861874570511082349 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2708884727561 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2708884727561 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2708884727561 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_582 :
    ((2588109640277317232227 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3802983355565918952933 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8234272398279661 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (430539689579888660491 / 1250000000000000000000 : ℝ))) -
              6 * (908320991664078785569 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (8678814966921 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8678814966921 / 12800000000000 : ℝ)) =
      Real.log (21478814966921 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8678814966921 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8750814966921 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2588109640277317232227 / 5000000000000000000000 : ℝ) ≤
      Real.log (21478814966921 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8750814966921 / 12800000000000 : ℝ) ≤
      (-(3802983355565918952933 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8750814966921 / 12800000000000 : ℝ) = (8750814966921 / 6400000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8750814966921 / 6400000000000 : ℝ) ≤
            (3128488447434081047067 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8234272398279661 / 10000000000000000 : ℝ) ≤ Real.sqrt (8678814966921 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8678814966921 / 12800000000000 : ℝ) ≤ (514642024892479 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8678814966921 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau936 :
    Real.arctan (8234272398279664 / 22953889065800675 : ℝ) ≤
      (430539689579888660491 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau935 :
    Real.arctan (514642024892479 / 625000000000000 : ℝ) ≤
      (2 * (430539689579888660491 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (518155562632027 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (514642024892479 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (514642024892479 / 625000000000000 : ℝ) /
                (1 + (518155562632027 / 400000000000000 : ℝ)) =
              (8234272398279664 / 22953889065800675 : ℝ)
            by
        norm_num];
        exact hau936)
  have hat1 :
    (Real.pi / 2 - (2 * (430539689579888660491 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 514642024892479 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 514642024892479 : ℝ) =
              (514642024892479 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau935)
  have hz1 :
    (625000000000000 / 514642024892479 : ℝ) ≤
      1 / Real.sqrt (8678814966921 / 12800000000000 : ℝ) := by
    rw [show (625000000000000 / 514642024892479 : ℝ) = 1 / (514642024892479 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8234272398279661 : ℝ) ≤
      (908320991664078785569 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8678814966921 / 12800000000000 : ℝ) ≤
      (750000000000000 / 8234272398279661 : ℝ) := by
    rw [show
        (750000000000000 / 8234272398279661 : ℝ) =
          (3 / 40) / (8234272398279661 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (430539689579888660491 / 1250000000000000000000 : ℝ))) -
        6 * (908320991664078785569 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8678814966921 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8678814966921 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8234272398279661 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (430539689579888660491 / 1250000000000000000000 : ℝ))) -
          6 * (908320991664078785569 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (8678814966921 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8678814966921 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8678814966921 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_583 :
    ((2590526284198282895123 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(473890531400934063847 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4119598453402819 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (430723063520010527707 / 1250000000000000000000 : ℝ))) -
              6 * (181556214657614903937 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (21722997014117 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21722997014117 / 32000000000000 : ℝ)) =
      Real.log (53722997014117 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21722997014117 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21902997014117 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2590526284198282895123 / 5000000000000000000000 : ℝ) ≤
      Real.log (53722997014117 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21902997014117 / 32000000000000 : ℝ) ≤
      (-(473890531400934063847 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21902997014117 / 32000000000000 : ℝ) = (21902997014117 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21902997014117 / 16000000000000 : ℝ) ≤
            (392543443974065936153 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4119598453402819 / 5000000000000000 : ℝ) ≤ Real.sqrt (21722997014117 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21722997014117 / 32000000000000 : ℝ) ≤
      (8239196906805641 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21722997014117 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau938 :
    Real.arctan (8239196906805641 / 22957019937821953 : ℝ) ≤
      (430723063520010527707 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau937 :
    Real.arctan (8239196906805641 / 10000000000000000 : ℝ) ≤
      (2 * (430723063520010527707 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12957019937821953 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8239196906805641 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8239196906805641 / 10000000000000000 : ℝ) /
                (1 + (12957019937821953 / 10000000000000000 : ℝ)) =
              (8239196906805641 / 22957019937821953 : ℝ)
            by
        norm_num];
        exact hau938)
  have hat1 :
    (Real.pi / 2 - (2 * (430723063520010527707 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8239196906805641 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8239196906805641 : ℝ) =
              (8239196906805641 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau937)
  have hz1 :
    (10000000000000000 / 8239196906805641 : ℝ) ≤
      1 / Real.sqrt (21722997014117 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8239196906805641 : ℝ) =
          1 / (8239196906805641 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4119598453402819 : ℝ) ≤
      (181556214657614903937 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21722997014117 / 32000000000000 : ℝ) ≤
      (375000000000000 / 4119598453402819 : ℝ) := by
    rw [show
        (375000000000000 / 4119598453402819 : ℝ) =
          (3 / 40) / (4119598453402819 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (430723063520010527707 / 1250000000000000000000 : ℝ))) -
        6 * (181556214657614903937 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21722997014117 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21722997014117 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4119598453402819 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (430723063520010527707 / 1250000000000000000000 : ℝ))) -
          6 * (181556214657614903937 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (21722997014117 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21722997014117 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21722997014117 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_584 :
    ((2592941760649929219989 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(755855838805518644779 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8244118473746051 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3447249915120971146511 / 10000000000000000000000 : ℝ))) -
              6 * (181448423315843392787 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (43497913221863 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43497913221863 / 64000000000000 : ℝ)) =
      Real.log (107497913221863 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43497913221863 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (43857913221863 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2592941760649929219989 / 5000000000000000000000 : ℝ) ≤
      Real.log (107497913221863 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (43857913221863 / 64000000000000 : ℝ) ≤
      (-(755855838805518644779 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43857913221863 / 64000000000000 : ℝ) = (43857913221863 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43857913221863 / 32000000000000 : ℝ) ≤
            (630438521794481355221 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8244118473746051 / 10000000000000000 : ℝ) ≤
      Real.sqrt (43497913221863 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43497913221863 / 64000000000000 : ℝ) ≤ (4122059236873027 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43497913221863 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau940 :
    Real.arctan (4122059236873027 / 11480075026748551 : ℝ) ≤
      (3447249915120971146511 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau939 :
    Real.arctan (4122059236873027 / 5000000000000000 : ℝ) ≤
      (2 * (3447249915120971146511 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6480075026748551 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4122059236873027 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4122059236873027 / 5000000000000000 : ℝ) /
                (1 + (6480075026748551 / 5000000000000000 : ℝ)) =
              (4122059236873027 / 11480075026748551 : ℝ)
            by
        norm_num];
        exact hau940)
  have hat1 :
    (Real.pi / 2 - (2 * (3447249915120971146511 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4122059236873027 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4122059236873027 : ℝ) =
              (4122059236873027 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau939)
  have hz1 :
    (5000000000000000 / 4122059236873027 : ℝ) ≤
      1 / Real.sqrt (43497913221863 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4122059236873027 : ℝ) = 1 / (4122059236873027 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8244118473746051 : ℝ) ≤
      (181448423315843392787 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43497913221863 / 64000000000000 : ℝ) ≤
      (750000000000000 / 8244118473746051 : ℝ) := by
    rw [show
        (750000000000000 / 8244118473746051 : ℝ) =
          (3 / 40) / (8244118473746051 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3447249915120971146511 / 10000000000000000000000 : ℝ))) -
        6 * (181448423315843392787 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43497913221863 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43497913221863 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8244118473746051 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3447249915120971146511 / 10000000000000000000000 : ℝ))) -
          6 * (181448423315843392787 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (43497913221863 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43497913221863 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43497913221863 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_585 :
    ((5190712141519418885757 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(75348963015754358381 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8249037104365953 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (215544608788683865353 / 625000000000000000000 : ℝ))) -
              6 * (113338014835763844939 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (10887458103873 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10887458103873 / 16000000000000 : ℝ)) =
      Real.log (26887458103873 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10887458103873 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10977458103873 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5190712141519418885757 / 10000000000000000000000 : ℝ) ≤
      Real.log (26887458103873 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10977458103873 / 16000000000000 : ℝ) ≤
      (-(75348963015754358381 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (10977458103873 / 16000000000000 : ℝ) = (10977458103873 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10977458103873 / 8000000000000 : ℝ) ≤
            (63280473044245641619 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8249037104365953 / 10000000000000000 : ℝ) ≤
      Real.sqrt (10887458103873 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10887458103873 / 16000000000000 : ℝ) ≤ (2062259276091489 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10887458103873 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau942 :
    Real.arctan (8249037104365956 / 22963279413374003 : ℝ) ≤
      (215544608788683865353 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau941 :
    Real.arctan (2062259276091489 / 2500000000000000 : ℝ) ≤
      (2 * (215544608788683865353 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12963279413374003 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2062259276091489 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2062259276091489 / 2500000000000000 : ℝ) /
                (1 + (12963279413374003 / 10000000000000000 : ℝ)) =
              (8249037104365956 / 22963279413374003 : ℝ)
            by
        norm_num];
        exact hau942)
  have hat1 :
    (Real.pi / 2 - (2 * (215544608788683865353 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2062259276091489 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2062259276091489 : ℝ) =
              (2062259276091489 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau941)
  have hz1 :
    (2500000000000000 / 2062259276091489 : ℝ) ≤
      1 / Real.sqrt (10887458103873 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2062259276091489 : ℝ) = 1 / (2062259276091489 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2749679034788651 : ℝ) ≤
      (113338014835763844939 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10887458103873 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2749679034788651 : ℝ) := by
    rw [show
        (250000000000000 / 2749679034788651 : ℝ) =
          (3 / 40) / (8249037104365953 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (215544608788683865353 / 625000000000000000000 : ℝ))) -
        6 * (113338014835763844939 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10887458103873 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10887458103873 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8249037104365953 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (215544608788683865353 / 625000000000000000000 : ℝ))) -
          6 * (113338014835763844939 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (10887458103873 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10887458103873 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10887458103873 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_586 :
    ((41564307450455109999 / 80000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3755631088367118116969 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1031744100489339 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1725087993871008903277 / 5000000000000000000000 : ℝ))) -
              6 * (1132708845961478349 / 12500000000000000000 : ℝ)))) ≤
      Vfield (43601751609121 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43601751609121 / 64000000000000 : ℝ)) =
      Real.log (107601751609121 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43601751609121 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (43961751609121 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (41564307450455109999 / 80000000000000000000 : ℝ) ≤
      Real.log (107601751609121 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (43961751609121 / 64000000000000 : ℝ) ≤
      (-(3755631088367118116969 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43961751609121 / 64000000000000 : ℝ) = (43961751609121 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43961751609121 / 32000000000000 : ℝ) ≤
            (3175840714632881883031 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1031744100489339 / 1250000000000000 : ℝ) ≤ Real.sqrt (43601751609121 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43601751609121 / 64000000000000 : ℝ) ≤ (1650790560782943 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43601751609121 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau944 :
    Real.arctan (2751317601304905 / 7655469339333293 : ℝ) ≤
      (1725087993871008903277 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau943 :
    Real.arctan (1650790560782943 / 2000000000000000 : ℝ) ≤
      (2 * (1725087993871008903277 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12966408017999879 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1650790560782943 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1650790560782943 / 2000000000000000 : ℝ) /
                (1 + (12966408017999879 / 10000000000000000 : ℝ)) =
              (2751317601304905 / 7655469339333293 : ℝ)
            by
        norm_num];
        exact hau944)
  have hat1 :
    (Real.pi / 2 - (2 * (1725087993871008903277 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1650790560782943 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1650790560782943 : ℝ) =
              (1650790560782943 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau943)
  have hz1 :
    (2000000000000000 / 1650790560782943 : ℝ) ≤
      1 / Real.sqrt (43601751609121 / 64000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1650790560782943 : ℝ) = 1 / (1650790560782943 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 343914700163113 : ℝ) ≤
      (1132708845961478349 / 12500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43601751609121 / 64000000000000 : ℝ) ≤
      (31250000000000 / 343914700163113 : ℝ) := by
    rw [show
        (31250000000000 / 343914700163113 : ℝ) =
          (3 / 40) / (1031744100489339 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1725087993871008903277 / 5000000000000000000000 : ℝ))) -
        6 * (1132708845961478349 / 12500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43601751609121 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43601751609121 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1031744100489339 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1725087993871008903277 / 5000000000000000000000 : ℝ))) -
          6 * (1132708845961478349 / 12500000000000000000 : ℝ))) ≤
      Real.sqrt (43601751609121 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43601751609121 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43601751609121 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_587 :
    ((2600181196455325552307 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(58497312090036620399 / 156250000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8258865577626073 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (53931822805767294657 / 156250000000000000000 : ℝ))) -
              6 * (226407747000154761683 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (174614683211 / 256000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (174614683211 / 256000000000 : ℝ)) =
      Real.log (430614683211 / 256000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((174614683211 / 256000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (176054683211 / 256000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2600181196455325552307 / 5000000000000000000000 : ℝ) ≤
      Real.log (430614683211 / 256000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (176054683211 / 256000000000 : ℝ) ≤
      (-(58497312090036620399 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (176054683211 / 256000000000 : ℝ) = (176054683211 / 128000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (176054683211 / 128000000000 : ℝ) ≤
            (49806934831838379601 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8258865577626073 / 10000000000000000 : ℝ) ≤ Real.sqrt (174614683211 / 256000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (174614683211 / 256000000000 : ℝ) ≤ (2064716394406519 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (174614683211 / 256000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau946 :
    Real.arctan (4129432788813038 / 11484767933960645 : ℝ) ≤
      (53931822805767294657 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau945 :
    Real.arctan (2064716394406519 / 2500000000000000 : ℝ) ≤
      (2 * (53931822805767294657 / 156250000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1296953586792129 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2064716394406519 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2064716394406519 / 2500000000000000 : ℝ) /
                (1 + (1296953586792129 / 1000000000000000 : ℝ)) =
              (4129432788813038 / 11484767933960645 : ℝ)
            by
        norm_num];
        exact hau946)
  have hat1 :
    (Real.pi / 2 - (2 * (53931822805767294657 / 156250000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2064716394406519 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2064716394406519 : ℝ) =
              (2064716394406519 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau945)
  have hz1 :
    (2500000000000000 / 2064716394406519 : ℝ) ≤ 1 / Real.sqrt (174614683211 / 256000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 2064716394406519 : ℝ) = 1 / (2064716394406519 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8258865577626073 : ℝ) ≤
      (226407747000154761683 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (174614683211 / 256000000000 : ℝ) ≤
      (750000000000000 / 8258865577626073 : ℝ) := by
    rw [show
        (750000000000000 / 8258865577626073 : ℝ) =
          (3 / 40) / (8258865577626073 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (53931822805767294657 / 156250000000000000000 : ℝ))) -
        6 * (226407747000154761683 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (174614683211 / 256000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (174614683211 / 256000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8258865577626073 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (53931822805767294657 / 156250000000000000000 : ℝ))) -
          6 * (226407747000154761683 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (174614683211 / 256000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (174614683211 / 256000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (174614683211 / 256000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_588 :
    ((2602592014287918378433 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1866019387043334946147 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((516485964419889 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (215818484948127477083 / 625000000000000000000 : ℝ))) -
              6 * (452547924782151544459 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (43705589996379 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43705589996379 / 64000000000000 : ℝ)) =
      Real.log (107705589996379 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43705589996379 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (44065589996379 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2602592014287918378433 / 5000000000000000000000 : ℝ) ≤
      Real.log (107705589996379 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (44065589996379 / 64000000000000 : ℝ) ≤
      (-(1866019387043334946147 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44065589996379 / 64000000000000 : ℝ) = (44065589996379 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44065589996379 / 32000000000000 : ℝ) ≤
            (1599716514456665053853 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (516485964419889 / 625000000000000 : ℝ) ≤ Real.sqrt (43705589996379 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43705589996379 / 64000000000000 : ℝ) ≤
      (8263775430718227 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43705589996379 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau948 :
    Real.arctan (1180539347245461 / 3281808994812020 : ℝ) ≤
      (215818484948127477083 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau947 :
    Real.arctan (8263775430718227 / 10000000000000000 : ℝ) ≤
      (2 * (215818484948127477083 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (648633148184207 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8263775430718227 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8263775430718227 / 10000000000000000 : ℝ) /
                (1 + (648633148184207 / 500000000000000 : ℝ)) =
              (1180539347245461 / 3281808994812020 : ℝ)
            by
        norm_num];
        exact hau948)
  have hat1 :
    (Real.pi / 2 - (2 * (215818484948127477083 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8263775430718227 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8263775430718227 : ℝ) =
              (8263775430718227 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau947)
  have hz1 :
    (10000000000000000 / 8263775430718227 : ℝ) ≤
      1 / Real.sqrt (43705589996379 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8263775430718227 : ℝ) =
          1 / (8263775430718227 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (15625000000000 / 172161988139963 : ℝ) ≤
      (452547924782151544459 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43705589996379 / 64000000000000 : ℝ) ≤
      (15625000000000 / 172161988139963 : ℝ) := by
    rw [show
        (15625000000000 / 172161988139963 : ℝ) =
          (3 / 40) / (516485964419889 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (215818484948127477083 / 625000000000000000000 : ℝ))) -
        6 * (452547924782151544459 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43705589996379 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43705589996379 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((516485964419889 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (215818484948127477083 / 625000000000000000000 : ℝ))) -
          6 * (452547924782151544459 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (43705589996379 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43705589996379 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43705589996379 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
