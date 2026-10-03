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

/-! # V06: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_73 :
    ((20176220250686091201 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2036763408608682511547 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((905658146596647 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (895944183790336958567 / 5000000000000000000000 : ℝ)) -
              6 * (785142011276042781277 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (262469337119 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (262469337119 / 8000000000000 : ℝ)) =
      Real.log (8262469337119 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((262469337119 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (307469337119 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (20176220250686091201 / 625000000000000000000 : ℝ) ≤
      Real.log (8262469337119 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (307469337119 / 8000000000000 : ℝ) ≤
      (-(2036763408608682511547 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (307469337119 / 8000000000000 : ℝ) = (307469337119 / 250000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (307469337119 / 250000000000 : ℝ) ≤
            (129321529828817488453 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (905658146596647 / 5000000000000000 : ℝ) ≤ Real.sqrt (262469337119 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (262469337119 / 8000000000000 : ℝ) ≤ (1811316293193297 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (262469337119 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau135 :
    Real.arctan (1811316293193297 / 10000000000000000 : ℝ) ≤
      (895944183790336958567 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (895944183790336958567 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1811316293193297 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1811316293193297 : ℝ) =
              (1811316293193297 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau135)
  have hz1 :
    (10000000000000000 / 1811316293193297 : ℝ) ≤
      1 / Real.sqrt (262469337119 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1811316293193297 : ℝ) =
          1 / (1811316293193297 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 301886048865549 : ℝ) ≤
      (785142011276042781277 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (262469337119 / 8000000000000 : ℝ) ≤
      (125000000000000 / 301886048865549 : ℝ) := by
    rw [show
        (125000000000000 / 301886048865549 : ℝ) =
          (3 / 40) / (905658146596647 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (895944183790336958567 / 5000000000000000000000 : ℝ)) -
        6 * (785142011276042781277 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (262469337119 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (262469337119 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((905658146596647 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (895944183790336958567 / 5000000000000000000000 : ℝ)) -
          6 * (785142011276042781277 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (262469337119 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (262469337119 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (262469337119 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_74 :
    ((332605631219046927529 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(32328510364068521412621 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1839018202329709 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1818697196560381043083 / 10000000000000000000000 : ℝ)) -
              6 * (3872349322266150066581 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (6763975897 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6763975897 / 200000000000 : ℝ)) = Real.log (206763975897 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6763975897 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7888975897 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (332605631219046927529 / 10000000000000000000000 : ℝ) ≤
      Real.log (206763975897 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7888975897 / 200000000000 : ℝ) ≤
      (-(32328510364068521412621 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (7888975897 / 200000000000 : ℝ) = (7888975897 / 6250000000 : ℝ) / 2 ^ 5 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7888975897 / 6250000000 : ℝ) ≤
            (2328848650931478587379 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1839018202329709 / 10000000000000000 : ℝ) ≤ Real.sqrt (6763975897 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6763975897 / 200000000000 : ℝ) ≤ (114938637645607 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6763975897 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau136 :
    Real.arctan (114938637645607 / 625000000000000 : ℝ) ≤
      (1818697196560381043083 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1818697196560381043083 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 114938637645607 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 114938637645607 : ℝ) =
              (114938637645607 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau136)
  have hz1 :
    (625000000000000 / 114938637645607 : ℝ) ≤ 1 / Real.sqrt (6763975897 / 200000000000 : ℝ) := by
    rw [show (625000000000000 / 114938637645607 : ℝ) = 1 / (114938637645607 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1839018202329709 : ℝ) ≤
      (3872349322266150066581 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6763975897 / 200000000000 : ℝ) ≤
      (750000000000000 / 1839018202329709 : ℝ) := by
    rw [show
        (750000000000000 / 1839018202329709 : ℝ) =
          (3 / 40) / (1839018202329709 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1818697196560381043083 / 10000000000000000000000 : ℝ)) -
        6 * (3872349322266150066581 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6763975897 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6763975897 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1839018202329709 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1818697196560381043083 / 10000000000000000000000 : ℝ)) -
          6 * (3872349322266150066581 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (6763975897 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6763975897 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6763975897 / 200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_75 :
    ((68476434199942366179 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(16037690220153861181957 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((466577243270909 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1845082320061846925631 / 10000000000000000000000 : ℝ)) -
              6 * (764222275881632837763 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (278648734641 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (278648734641 / 8000000000000 : ℝ)) =
      Real.log (8278648734641 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((278648734641 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (323648734641 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (68476434199942366179 / 2000000000000000000000 : ℝ) ≤
      Real.log (8278648734641 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (323648734641 / 8000000000000 : ℝ) ≤
      (-(16037690220153861181957 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (323648734641 / 8000000000000 : ℝ) = (323648734641 / 250000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (323648734641 / 250000000000 : ℝ) ≤
            (1290989287346138818043 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (466577243270909 / 2500000000000000 : ℝ) ≤ Real.sqrt (278648734641 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (278648734641 / 8000000000000 : ℝ) ≤ (1866308973083639 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (278648734641 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau137 :
    Real.arctan (1866308973083639 / 10000000000000000 : ℝ) ≤
      (1845082320061846925631 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1845082320061846925631 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1866308973083639 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1866308973083639 : ℝ) =
              (1866308973083639 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau137)
  have hz1 :
    (10000000000000000 / 1866308973083639 : ℝ) ≤
      1 / Real.sqrt (278648734641 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1866308973083639 : ℝ) =
          1 / (1866308973083639 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 466577243270909 : ℝ) ≤
      (764222275881632837763 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (278648734641 / 8000000000000 : ℝ) ≤
      (187500000000000 / 466577243270909 : ℝ) := by
    rw [show
        (187500000000000 / 466577243270909 : ℝ) =
          (3 / 40) / (466577243270909 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1845082320061846925631 / 10000000000000000000000 : ℝ)) -
        6 * (764222275881632837763 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (278648734641 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (278648734641 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((466577243270909 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1845082320061846925631 / 10000000000000000000000 : ℝ)) -
          6 * (764222275881632837763 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (278648734641 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (278648734641 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (278648734641 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_76 :
    ((352149162041970693603 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7957125030406035210083 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((75728255413947 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (935530869456240818211 / 5000000000000000000000 : ℝ)) -
              6 * (3771858836909198659297 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (143369216701 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (143369216701 / 4000000000000 : ℝ)) =
      Real.log (4143369216701 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((143369216701 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (165869216701 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (352149162041970693603 / 10000000000000000000000 : ℝ) ≤
      Real.log (4143369216701 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (165869216701 / 4000000000000 : ℝ) ≤
      (-(7957125030406035210083 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (165869216701 / 4000000000000 : ℝ) = (165869216701 / 125000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (165869216701 / 125000000000 : ℝ) ≤
            (707214723343964789917 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (75728255413947 / 400000000000000 : ℝ) ≤ Real.sqrt (143369216701 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (143369216701 / 4000000000000 : ℝ) ≤ (946603192674339 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (143369216701 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau138 :
    Real.arctan (946603192674339 / 5000000000000000 : ℝ) ≤
      (935530869456240818211 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (935530869456240818211 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 946603192674339 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 946603192674339 : ℝ) =
              (946603192674339 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau138)
  have hz1 :
    (5000000000000000 / 946603192674339 : ℝ) ≤ 1 / Real.sqrt (143369216701 / 4000000000000 : ℝ) :=
  by
    rw [show
        (5000000000000000 / 946603192674339 : ℝ) = 1 / (946603192674339 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (10000000000000 / 25242751804649 : ℝ) ≤
      (3771858836909198659297 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (143369216701 / 4000000000000 : ℝ) ≤
      (10000000000000 / 25242751804649 : ℝ) := by
    rw [show
        (10000000000000 / 25242751804649 : ℝ) = (3 / 40) / (75728255413947 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (935530869456240818211 / 5000000000000000000000 : ℝ)) -
        6 * (3771858836909198659297 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (143369216701 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (143369216701 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((75728255413947 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (935530869456240818211 / 5000000000000000000000 : ℝ)) -
          6 * (3771858836909198659297 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (143369216701 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (143369216701 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (143369216701 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_77 :
    ((371654572393941879647 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(313523048550250673131 / 100000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1945886144292619 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (48046732795733132627 / 250000000000000000000 : ℝ)) -
              6 * (183940991600097138117 / 500000000000000000000 : ℝ)))) ≤
      Vfield (75729457731 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (75729457731 / 2000000000000 : ℝ)) =
      Real.log (2075729457731 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((75729457731 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (86979457731 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (371654572393941879647 / 10000000000000000000000 : ℝ) ≤
      Real.log (2075729457731 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (86979457731 / 2000000000000 : ℝ) ≤
      (-(313523048550250673131 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (86979457731 / 2000000000000 : ℝ) = (86979457731 / 62500000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (86979457731 / 62500000000 : ℝ) ≤
            (33050541599749326869 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1945886144292619 / 10000000000000000 : ℝ) ≤ Real.sqrt (75729457731 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (75729457731 / 2000000000000 : ℝ) ≤ (972943072146311 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (75729457731 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau139 :
    Real.arctan (972943072146311 / 5000000000000000 : ℝ) ≤
      (48046732795733132627 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (48046732795733132627 / 250000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 972943072146311 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 972943072146311 : ℝ) =
              (972943072146311 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau139)
  have hz1 :
    (5000000000000000 / 972943072146311 : ℝ) ≤ 1 / Real.sqrt (75729457731 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 972943072146311 : ℝ) = 1 / (972943072146311 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1945886144292619 : ℝ) ≤
      (183940991600097138117 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (75729457731 / 2000000000000 : ℝ) ≤
      (750000000000000 / 1945886144292619 : ℝ) := by
    rw [show
        (750000000000000 / 1945886144292619 : ℝ) =
          (3 / 40) / (1945886144292619 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (48046732795733132627 / 250000000000000000000 : ℝ)) -
        6 * (183940991600097138117 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (75729457731 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (75729457731 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1945886144292619 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (48046732795733132627 / 250000000000000000000 : ℝ)) -
          6 * (183940991600097138117 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (75729457731 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (75729457731 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (75729457731 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_78 :
    ((51318953063325241837 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15231489342023646879373 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((409436579929053 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2019282332713757840697 / 10000000000000000000000 : ℝ)) -
              6 * (877929728397766997881 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (20954789123 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20954789123 / 500000000000 : ℝ)) =
      Real.log (520954789123 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20954789123 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23767289123 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (51318953063325241837 / 1250000000000000000000 : ℝ) ≤
      Real.log (520954789123 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23767289123 / 500000000000 : ℝ) ≤
      (-(15231489342023646879373 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (23767289123 / 500000000000 : ℝ) = (23767289123 / 15625000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23767289123 / 15625000000 : ℝ) ≤
            (2097190165476353120627 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (409436579929053 / 2000000000000000 : ℝ) ≤ Real.sqrt (20954789123 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20954789123 / 500000000000 : ℝ) ≤ (511795724911317 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20954789123 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau140 :
    Real.arctan (511795724911317 / 2500000000000000 : ℝ) ≤
      (2019282332713757840697 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2019282332713757840697 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 511795724911317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 511795724911317 : ℝ) =
              (511795724911317 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau140)
  have hz1 :
    (2500000000000000 / 511795724911317 : ℝ) ≤ 1 / Real.sqrt (20954789123 / 500000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 511795724911317 : ℝ) = 1 / (511795724911317 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 136478859976351 : ℝ) ≤
      (877929728397766997881 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20954789123 / 500000000000 : ℝ) ≤
      (50000000000000 / 136478859976351 : ℝ) := by
    rw [show
        (50000000000000 / 136478859976351 : ℝ) =
          (3 / 40) / (409436579929053 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2019282332713757840697 / 10000000000000000000000 : ℝ)) -
        6 * (877929728397766997881 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20954789123 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20954789123 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((409436579929053 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2019282332713757840697 / 10000000000000000000000 : ℝ)) -
          6 * (877929728397766997881 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (20954789123 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20954789123 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20954789123 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_79 :
    ((26556429962361706593 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1884565064399020768501 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((16276631329523 / 78125000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2054026228998431747243 / 10000000000000000000000 : ℝ)) -
              6 * (431930043648711482693 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (694494763253 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (694494763253 / 16000000000000 : ℝ)) =
      Real.log (16694494763253 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((694494763253 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (784494763253 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (26556429962361706593 / 625000000000000000000 : ℝ) ≤
      Real.log (16694494763253 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (784494763253 / 16000000000000 : ℝ) ≤
      (-(1884565064399020768501 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (784494763253 / 16000000000000 : ℝ) = (784494763253 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (784494763253 / 500000000000 : ℝ) ≤
            (281519874038479231499 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (16276631329523 / 78125000000000 : ℝ) ≤ Real.sqrt (694494763253 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (694494763253 / 16000000000000 : ℝ) ≤ (2083408810178947 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (694494763253 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau141 :
    Real.arctan (2083408810178947 / 10000000000000000 : ℝ) ≤
      (2054026228998431747243 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2054026228998431747243 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2083408810178947 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2083408810178947 : ℝ) =
              (2083408810178947 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau141)
  have hz1 :
    (10000000000000000 / 2083408810178947 : ℝ) ≤
      1 / Real.sqrt (694494763253 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2083408810178947 : ℝ) =
          1 / (2083408810178947 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (5859375000000 / 16276631329523 : ℝ) ≤
      (431930043648711482693 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (694494763253 / 16000000000000 : ℝ) ≤
      (5859375000000 / 16276631329523 : ℝ) := by
    rw [show
        (5859375000000 / 16276631329523 : ℝ) = (3 / 40) / (16276631329523 / 78125000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2054026228998431747243 / 10000000000000000000000 : ℝ)) -
        6 * (431930043648711482693 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (694494763253 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (694494763253 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((16276631329523 / 78125000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2054026228998431747243 / 10000000000000000000000 : ℝ)) -
          6 * (431930043648711482693 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (694494763253 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (694494763253 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (694494763253 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_80 :
    ((54008848847639878331 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(30001601622668503149493 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2101287579841671 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (258894388269868848451 / 1250000000000000000000 : ℝ)) -
              6 * (1714149204325831240059 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1412931037823 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1412931037823 / 32000000000000 : ℝ)) =
      Real.log (33412931037823 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1412931037823 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1592931037823 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (54008848847639878331 / 1250000000000000000000 : ℝ) ≤
      Real.log (33412931037823 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1592931037823 / 32000000000000 : ℝ) ≤
      (-(30001601622668503149493 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1592931037823 / 32000000000000 : ℝ) = (1592931037823 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1592931037823 / 1000000000000 : ℝ) ≤
            (4655757392331496850507 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2101287579841671 / 10000000000000000 : ℝ) ≤ Real.sqrt (1412931037823 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1412931037823 / 32000000000000 : ℝ) ≤ (1050643789920837 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1412931037823 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau142 :
    Real.arctan (1050643789920837 / 5000000000000000 : ℝ) ≤
      (258894388269868848451 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (258894388269868848451 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1050643789920837 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1050643789920837 : ℝ) =
              (1050643789920837 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau142)
  have hz1 :
    (5000000000000000 / 1050643789920837 : ℝ) ≤
      1 / Real.sqrt (1412931037823 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1050643789920837 : ℝ) = 1 / (1050643789920837 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 700429193280557 : ℝ) ≤
      (1714149204325831240059 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1412931037823 / 32000000000000 : ℝ) ≤
      (250000000000000 / 700429193280557 : ℝ) := by
    rw [show
        (250000000000000 / 700429193280557 : ℝ) =
          (3 / 40) / (2101287579841671 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (258894388269868848451 / 1250000000000000000000 : ℝ)) -
        6 * (1714149204325831240059 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1412931037823 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1412931037823 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2101287579841671 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (258894388269868848451 / 1250000000000000000000 : ℝ)) -
          6 * (1714149204325831240059 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1412931037823 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1412931037823 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1412931037823 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_81 :
    ((219616783974515609901 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1492621071671766733419 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((105950775316447 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1044063650657751722727 / 5000000000000000000000 : ℝ)) -
              6 * (850446742255768075683 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (71843627457 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (71843627457 / 1600000000000 : ℝ)) =
      Real.log (1671843627457 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((71843627457 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (80843627457 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (219616783974515609901 / 5000000000000000000000 : ℝ) ≤
      Real.log (1671843627457 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (80843627457 / 1600000000000 : ℝ) ≤
      (-(1492621071671766733419 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (80843627457 / 1600000000000 : ℝ) = (80843627457 / 50000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (80843627457 / 50000000000 : ℝ) ≤
            (240246879078233266581 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (105950775316447 / 500000000000000 : ℝ) ≤ Real.sqrt (71843627457 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (71843627457 / 1600000000000 : ℝ) ≤ (2119015506328943 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (71843627457 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau143 :
    Real.arctan (2119015506328943 / 10000000000000000 : ℝ) ≤
      (1044063650657751722727 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1044063650657751722727 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2119015506328943 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2119015506328943 : ℝ) =
              (2119015506328943 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau143)
  have hz1 :
    (10000000000000000 / 2119015506328943 : ℝ) ≤
      1 / Real.sqrt (71843627457 / 1600000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2119015506328943 : ℝ) =
          1 / (2119015506328943 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (37500000000000 / 105950775316447 : ℝ) ≤
      (850446742255768075683 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (71843627457 / 1600000000000 : ℝ) ≤
      (37500000000000 / 105950775316447 : ℝ) := by
    rw [show
        (37500000000000 / 105950775316447 : ℝ) =
          (3 / 40) / (105950775316447 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1044063650657751722727 / 5000000000000000000000 : ℝ)) -
        6 * (850446742255768075683 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (71843627457 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (71843627457 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((105950775316447 / 500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1044063650657751722727 / 5000000000000000000000 : ℝ)) -
          6 * (850446742255768075683 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (71843627457 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (71843627457 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (71843627457 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_82 :
    ((442813033499629176129 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14889328837725568225533 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1063912041417817 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1048277920962015937779 / 5000000000000000000000 : ℝ)) -
              6 * (3388760114959635706763 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2897686609597 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2897686609597 / 64000000000000 : ℝ)) =
      Real.log (66897686609597 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2897686609597 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3257686609597 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (442813033499629176129 / 10000000000000000000000 : ℝ) ≤
      Real.log (66897686609597 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3257686609597 / 64000000000000 : ℝ) ≤
      (-(14889328837725568225533 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (3257686609597 / 64000000000000 : ℝ) = (3257686609597 / 2000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3257686609597 / 2000000000000 : ℝ) ≤
            (2439350669774431774467 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1063912041417817 / 5000000000000000 : ℝ) ≤ Real.sqrt (2897686609597 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2897686609597 / 64000000000000 : ℝ) ≤ (2127824082835637 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2897686609597 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau144 :
    Real.arctan (2127824082835637 / 10000000000000000 : ℝ) ≤
      (1048277920962015937779 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1048277920962015937779 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2127824082835637 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2127824082835637 : ℝ) =
              (2127824082835637 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau144)
  have hz1 :
    (10000000000000000 / 2127824082835637 : ℝ) ≤
      1 / Real.sqrt (2897686609597 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2127824082835637 : ℝ) =
          1 / (2127824082835637 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1063912041417817 : ℝ) ≤
      (3388760114959635706763 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2897686609597 / 64000000000000 : ℝ) ≤
      (375000000000000 / 1063912041417817 : ℝ) := by
    rw [show
        (375000000000000 / 1063912041417817 : ℝ) =
          (3 / 40) / (1063912041417817 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1048277920962015937779 / 5000000000000000000000 : ℝ)) -
        6 * (3388760114959635706763 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2897686609597 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2897686609597 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1063912041417817 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1048277920962015937779 / 5000000000000000000000 : ℝ)) -
          6 * (3388760114959635706763 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2897686609597 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2897686609597 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2897686609597 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_83 :
    ((223195609125654108827 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2970543404491423273459 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1068298172202887 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1052473315449602418319 / 5000000000000000000000 : ℝ)) -
              6 * (1687940980739126299293 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1460814060457 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1460814060457 / 32000000000000 : ℝ)) =
      Real.log (33460814060457 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1460814060457 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1640814060457 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (223195609125654108827 / 5000000000000000000000 : ℝ) ≤
      Real.log (33460814060457 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1640814060457 / 32000000000000 : ℝ) ≤
      (-(2970543404491423273459 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1640814060457 / 32000000000000 : ℝ) = (1640814060457 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1640814060457 / 1000000000000 : ℝ) ≤
            (495192497008576726541 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1068298172202887 / 5000000000000000 : ℝ) ≤ Real.sqrt (1460814060457 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1460814060457 / 32000000000000 : ℝ) ≤ (2136596344405777 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1460814060457 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau145 :
    Real.arctan (2136596344405777 / 10000000000000000 : ℝ) ≤
      (1052473315449602418319 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1052473315449602418319 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2136596344405777 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2136596344405777 : ℝ) =
              (2136596344405777 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau145)
  have hz1 :
    (10000000000000000 / 2136596344405777 : ℝ) ≤
      1 / Real.sqrt (1460814060457 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2136596344405777 : ℝ) =
          1 / (2136596344405777 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1068298172202887 : ℝ) ≤
      (1687940980739126299293 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1460814060457 / 32000000000000 : ℝ) ≤
      (375000000000000 / 1068298172202887 : ℝ) := by
    rw [show
        (375000000000000 / 1068298172202887 : ℝ) =
          (3 / 40) / (1068298172202887 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1052473315449602418319 / 5000000000000000000000 : ℝ)) -
        6 * (1687940980739126299293 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1460814060457 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1460814060457 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1068298172202887 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1052473315449602418319 / 5000000000000000000000 : ℝ)) -
          6 * (1687940980739126299293 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1460814060457 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1460814060457 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1460814060457 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_84 :
    ((449968123120327541017 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29632742689235428438627 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((536333184128633 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2113300121198763880449 / 10000000000000000000000 : ℝ)) -
              6 * (420393712183787165013 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (2945569632231 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2945569632231 / 64000000000000 : ℝ)) =
      Real.log (66945569632231 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2945569632231 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3305569632231 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (449968123120327541017 / 10000000000000000000000 : ℝ) ≤
      Real.log (66945569632231 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3305569632231 / 64000000000000 : ℝ) ≤
      (-(29632742689235428438627 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (3305569632231 / 64000000000000 : ℝ) = (3305569632231 / 2000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3305569632231 / 2000000000000 : ℝ) ≤
            (5024616325764571561373 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (536333184128633 / 2500000000000000 : ℝ) ≤ Real.sqrt (2945569632231 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2945569632231 / 64000000000000 : ℝ) ≤ (429066547302907 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2945569632231 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau146 :
    Real.arctan (429066547302907 / 2000000000000000 : ℝ) ≤
      (2113300121198763880449 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2113300121198763880449 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 429066547302907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 429066547302907 : ℝ) =
              (429066547302907 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau146)
  have hz1 :
    (2000000000000000 / 429066547302907 : ℝ) ≤
      1 / Real.sqrt (2945569632231 / 64000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 429066547302907 : ℝ) = 1 / (429066547302907 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 536333184128633 : ℝ) ≤
      (420393712183787165013 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2945569632231 / 64000000000000 : ℝ) ≤
      (187500000000000 / 536333184128633 : ℝ) := by
    rw [show
        (187500000000000 / 536333184128633 : ℝ) =
          (3 / 40) / (536333184128633 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2113300121198763880449 / 10000000000000000000000 : ℝ)) -
        6 * (420393712183787165013 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2945569632231 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2945569632231 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((536333184128633 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2113300121198763880449 / 10000000000000000000000 : ℝ)) -
          6 * (420393712183787165013 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (2945569632231 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2945569632231 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2945569632231 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
