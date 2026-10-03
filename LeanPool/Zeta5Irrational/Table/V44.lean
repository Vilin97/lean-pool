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

/-! # V44: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_529 :
    ((4732002263155807105589 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(986142542453729802313 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3889481773370539 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) -
              6 * (192233570110948262549 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (38727855271377 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38727855271377 / 64000000000000 : ℝ)) =
      Real.log (102727855271377 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38727855271377 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39087855271377 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4732002263155807105589 / 10000000000000000000000 : ℝ) ≤
      Real.log (102727855271377 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39087855271377 / 64000000000000 : ℝ) ≤
      (-(986142542453729802313 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39087855271377 / 64000000000000 : ℝ) = (39087855271377 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39087855271377 / 32000000000000 : ℝ) ≤
            (400151818146270197687 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3889481773370539 / 5000000000000000 : ℝ) ≤ Real.sqrt (38727855271377 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38727855271377 / 64000000000000 : ℝ) ≤
      (7778963546741081 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38727855271377 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau830 :
    Real.arctan (7778963546741081 / 22669343860734325 : ℝ) ≤
      (661117047132910503789 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau829 :
    Real.arctan (7778963546741081 / 10000000000000000 : ℝ) ≤
      (2 * (661117047132910503789 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (506773754429373 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (7778963546741081 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7778963546741081 / 10000000000000000 : ℝ) /
                (1 + (506773754429373 / 400000000000000 : ℝ)) =
              (7778963546741081 / 22669343860734325 : ℝ)
            by
        norm_num];
        exact hau830)
  have hat1 :
    (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7778963546741081 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7778963546741081 : ℝ) =
              (7778963546741081 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau829)
  have hz1 :
    (10000000000000000 / 7778963546741081 : ℝ) ≤
      1 / Real.sqrt (38727855271377 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7778963546741081 : ℝ) =
          1 / (7778963546741081 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3889481773370539 : ℝ) ≤
      (192233570110948262549 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38727855271377 / 64000000000000 : ℝ) ≤
      (375000000000000 / 3889481773370539 : ℝ) := by
    rw [show
        (375000000000000 / 3889481773370539 : ℝ) =
          (3 / 40) / (3889481773370539 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) -
        6 * (192233570110948262549 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38727855271377 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38727855271377 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3889481773370539 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) -
          6 * (192233570110948262549 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (38727855271377 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38727855271377 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38727855271377 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_530 :
    ((4738696609226712308587 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4913128698083634611777 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3892934699771517 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3307735707316062547853 / 10000000000000000000000 : ℝ))) -
              6 * (960320555090723355467 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19398323938157 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19398323938157 / 32000000000000 : ℝ)) =
      Real.log (51398323938157 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19398323938157 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19578323938157 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4738696609226712308587 / 10000000000000000000000 : ℝ) ≤
      Real.log (51398323938157 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19578323938157 / 32000000000000 : ℝ) ≤
      (-(4913128698083634611777 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19578323938157 / 32000000000000 : ℝ) = (19578323938157 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19578323938157 / 16000000000000 : ℝ) ≤
            (2018343104916365388223 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3892934699771517 / 5000000000000000 : ℝ) ≤ Real.sqrt (19398323938157 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19398323938157 / 32000000000000 : ℝ) ≤
      (7785869399543037 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19398323938157 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau832 :
    Real.arctan (7785869399543037 / 22673585219137504 : ℝ) ≤
      (3307735707316062547853 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau831 :
    Real.arctan (7785869399543037 / 10000000000000000 : ℝ) ≤
      (2 * (3307735707316062547853 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (396049538098047 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (7785869399543037 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7785869399543037 / 10000000000000000 : ℝ) /
                (1 + (396049538098047 / 312500000000000 : ℝ)) =
              (7785869399543037 / 22673585219137504 : ℝ)
            by
        norm_num];
        exact hau832)
  have hat1 :
    (Real.pi / 2 - (2 * (3307735707316062547853 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7785869399543037 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7785869399543037 : ℝ) =
              (7785869399543037 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau831)
  have hz1 :
    (10000000000000000 / 7785869399543037 : ℝ) ≤
      1 / Real.sqrt (19398323938157 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7785869399543037 : ℝ) =
          1 / (7785869399543037 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1297644899923839 : ℝ) ≤
      (960320555090723355467 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19398323938157 / 32000000000000 : ℝ) ≤
      (125000000000000 / 1297644899923839 : ℝ) := by
    rw [show
        (125000000000000 / 1297644899923839 : ℝ) =
          (3 / 40) / (3892934699771517 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3307735707316062547853 / 10000000000000000000000 : ℝ))) -
        6 * (960320555090723355467 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19398323938157 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19398323938157 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3892934699771517 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3307735707316062547853 / 10000000000000000000000 : ℝ))) -
          6 * (960320555090723355467 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (19398323938157 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19398323938157 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19398323938157 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_531 :
    ((474538647686853408261 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4895575549388124547303 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((974096141558569 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3309882835885235928563 / 10000000000000000000000 : ℝ))) -
              6 * (479737748220980712743 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (38865440481251 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38865440481251 / 64000000000000 : ℝ)) =
      Real.log (102865440481251 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38865440481251 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39225440481251 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (474538647686853408261 / 1000000000000000000000 : ℝ) ≤
      Real.log (102865440481251 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39225440481251 / 64000000000000 : ℝ) ≤
      (-(4895575549388124547303 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39225440481251 / 64000000000000 : ℝ) = (39225440481251 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39225440481251 / 32000000000000 : ℝ) ≤
            (2035896253611875452697 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (974096141558569 / 1250000000000000 : ℝ) ≤ Real.sqrt (38865440481251 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38865440481251 / 64000000000000 : ℝ) ≤ (1558553826493711 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38865440481251 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau834 :
    Real.arctan (1558553826493711 / 4535565031719397 : ℝ) ≤
      (3309882835885235928563 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau833 :
    Real.arctan (1558553826493711 / 2000000000000000 : ℝ) ≤
      (2 * (3309882835885235928563 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2535565031719397 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1558553826493711 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1558553826493711 / 2000000000000000 : ℝ) /
                (1 + (2535565031719397 / 2000000000000000 : ℝ)) =
              (1558553826493711 / 4535565031719397 : ℝ)
            by
        norm_num];
        exact hau834)
  have hat1 :
    (Real.pi / 2 - (2 * (3309882835885235928563 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1558553826493711 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1558553826493711 : ℝ) =
              (1558553826493711 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau833)
  have hz1 :
    (2000000000000000 / 1558553826493711 : ℝ) ≤
      1 / Real.sqrt (38865440481251 / 64000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1558553826493711 : ℝ) = 1 / (1558553826493711 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 974096141558569 : ℝ) ≤
      (479737748220980712743 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38865440481251 / 64000000000000 : ℝ) ≤
      (93750000000000 / 974096141558569 : ℝ) := by
    rw [show
        (93750000000000 / 974096141558569 : ℝ) =
          (3 / 40) / (974096141558569 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3309882835885235928563 / 10000000000000000000000 : ℝ))) -
        6 * (479737748220980712743 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38865440481251 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38865440481251 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((974096141558569 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3309882835885235928563 / 10000000000000000000000 : ℝ))) -
          6 * (479737748220980712743 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (38865440481251 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38865440481251 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38865440481251 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_532 :
    ((4752071872069286534347 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2439026579007312957233 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1949915690439729 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3312026630892787282743 / 10000000000000000000000 : ℝ))) -
              6 * (479316332391940315167 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9733558271547 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9733558271547 / 16000000000000 : ℝ)) =
      Real.log (25733558271547 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9733558271547 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9823558271547 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4752071872069286534347 / 10000000000000000000000 : ℝ) ≤
      Real.log (25733558271547 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9823558271547 / 16000000000000 : ℝ) ≤
      (-(2439026579007312957233 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9823558271547 / 16000000000000 : ℝ) = (9823558271547 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9823558271547 / 8000000000000 : ℝ) ≤
            (1026709322492687042767 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1949915690439729 / 2500000000000000 : ℝ) ≤ Real.sqrt (9733558271547 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9733558271547 / 16000000000000 : ℝ) ≤ (7799662761758919 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9733558271547 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau836 :
    Real.arctan (7799662761758919 / 22682063680535938 : ℝ) ≤
      (3312026630892787282743 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau835 :
    Real.arctan (7799662761758919 / 10000000000000000 : ℝ) ≤
      (2 * (3312026630892787282743 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6341031840267969 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7799662761758919 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7799662761758919 / 10000000000000000 : ℝ) /
                (1 + (6341031840267969 / 5000000000000000 : ℝ)) =
              (7799662761758919 / 22682063680535938 : ℝ)
            by
        norm_num];
        exact hau836)
  have hat1 :
    (Real.pi / 2 - (2 * (3312026630892787282743 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7799662761758919 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7799662761758919 : ℝ) =
              (7799662761758919 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau835)
  have hz1 :
    (10000000000000000 / 7799662761758919 : ℝ) ≤
      1 / Real.sqrt (9733558271547 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7799662761758919 : ℝ) =
          1 / (7799662761758919 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 649971896813243 : ℝ) ≤
      (479316332391940315167 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9733558271547 / 16000000000000 : ℝ) ≤
      (62500000000000 / 649971896813243 : ℝ) := by
    rw [show
        (62500000000000 / 649971896813243 : ℝ) =
          (3 / 40) / (1949915690439729 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3312026630892787282743 / 10000000000000000000000 : ℝ))) -
        6 * (479316332391940315167 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9733558271547 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9733558271547 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1949915690439729 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3312026630892787282743 / 10000000000000000000000 : ℝ))) -
          6 * (479316332391940315167 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9733558271547 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9733558271547 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9733558271547 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_533 :
    ((594844100100622765061 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(972112283272651519513 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3903275151791851 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3314167101818064698889 / 10000000000000000000000 : ℝ))) -
              6 * (239448012588053166339 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (312024205529 / 512000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (312024205529 / 512000000000 : ℝ)) =
      Real.log (824024205529 / 512000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((312024205529 / 512000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (314904205529 / 512000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (594844100100622765061 / 1250000000000000000000 : ℝ) ≤
      Real.log (824024205529 / 512000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (314904205529 / 512000000000 : ℝ) ≤
      (-(972112283272651519513 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (314904205529 / 512000000000 : ℝ) = (314904205529 / 256000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (314904205529 / 256000000000 : ℝ) ≤
            (414182077327348480487 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3903275151791851 / 5000000000000000 : ℝ) ≤ Real.sqrt (312024205529 / 512000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (312024205529 / 512000000000 : ℝ) ≤ (1561310060716741 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (312024205529 / 512000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau838 :
    Real.arctan (7806550303583705 / 22686300786375152 : ℝ) ≤
      (3314167101818064698889 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau837 :
    Real.arctan (1561310060716741 / 2000000000000000 : ℝ) ≤
      (2 * (3314167101818064698889 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (792893799148447 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (1561310060716741 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1561310060716741 / 2000000000000000 : ℝ) /
                (1 + (792893799148447 / 625000000000000 : ℝ)) =
              (7806550303583705 / 22686300786375152 : ℝ)
            by
        norm_num];
        exact hau838)
  have hat1 :
    (Real.pi / 2 - (2 * (3314167101818064698889 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1561310060716741 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1561310060716741 : ℝ) =
              (1561310060716741 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau837)
  have hz1 :
    (2000000000000000 / 1561310060716741 : ℝ) ≤ 1 / Real.sqrt (312024205529 / 512000000000 : ℝ) :=
  by
    rw [show
        (2000000000000000 / 1561310060716741 : ℝ) = 1 / (1561310060716741 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3903275151791851 : ℝ) ≤
      (239448012588053166339 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (312024205529 / 512000000000 : ℝ) ≤
      (375000000000000 / 3903275151791851 : ℝ) := by
    rw [show
        (375000000000000 / 3903275151791851 : ℝ) =
          (3 / 40) / (3903275151791851 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3314167101818064698889 / 10000000000000000000000 : ℝ))) -
        6 * (239448012588053166339 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (312024205529 / 512000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (312024205529 / 512000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3903275151791851 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3314167101818064698889 / 10000000000000000000000 : ℝ))) -
          6 * (239448012588053166339 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (312024205529 / 512000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (312024205529 / 512000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (312024205529 / 512000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_534 :
    ((953085853807932739837 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4843100217397785791881 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1562686354808243 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (829076064524823682427 / 2500000000000000000000 : ℝ))) -
              6 * (956953643442521360779 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19535909148031 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19535909148031 / 32000000000000 : ℝ)) =
      Real.log (51535909148031 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19535909148031 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19715909148031 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (953085853807932739837 / 2000000000000000000000 : ℝ) ≤
      Real.log (51535909148031 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19715909148031 / 32000000000000 : ℝ) ≤
      (-(4843100217397785791881 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19715909148031 / 32000000000000 : ℝ) = (19715909148031 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19715909148031 / 16000000000000 : ℝ) ≤
            (2088371585602214208119 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1562686354808243 / 2000000000000000 : ℝ) ≤ Real.sqrt (19535909148031 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19535909148031 / 32000000000000 : ℝ) ≤ (3906715887020609 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19535909148031 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau840 :
    Real.arctan (3906715887020609 / 11345268238766523 : ℝ) ≤
      (829076064524823682427 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau839 :
    Real.arctan (3906715887020609 / 5000000000000000 : ℝ) ≤
      (2 * (829076064524823682427 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6345268238766523 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3906715887020609 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3906715887020609 / 5000000000000000 : ℝ) /
                (1 + (6345268238766523 / 5000000000000000 : ℝ)) =
              (3906715887020609 / 11345268238766523 : ℝ)
            by
        norm_num];
        exact hau840)
  have hat1 :
    (Real.pi / 2 - (2 * (829076064524823682427 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3906715887020609 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3906715887020609 : ℝ) =
              (3906715887020609 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau839)
  have hz1 :
    (5000000000000000 / 3906715887020609 : ℝ) ≤
      1 / Real.sqrt (19535909148031 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3906715887020609 : ℝ) = 1 / (3906715887020609 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1562686354808243 : ℝ) ≤
      (956953643442521360779 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19535909148031 / 32000000000000 : ℝ) ≤
      (150000000000000 / 1562686354808243 : ℝ) := by
    rw [show
        (150000000000000 / 1562686354808243 : ℝ) =
          (3 / 40) / (1562686354808243 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (829076064524823682427 / 2500000000000000000000 : ℝ))) -
        6 * (956953643442521360779 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19535909148031 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19535909148031 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1562686354808243 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (829076064524823682427 / 2500000000000000000000 : ℝ))) -
          6 * (956953643442521360779 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (19535909148031 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19535909148031 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19535909148031 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_535 :
    ((4772101282725436474587 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4825669454641694078661 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3910153594579467 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (829609527283457739137 / 2500000000000000000000 : ℝ))) -
              6 * (478058717204865695451 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (39140610900999 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (39140610900999 / 64000000000000 : ℝ)) =
      Real.log (103140610900999 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((39140610900999 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39500610900999 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4772101282725436474587 / 10000000000000000000000 : ℝ) ≤
      Real.log (103140610900999 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39500610900999 / 64000000000000 : ℝ) ≤
      (-(4825669454641694078661 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39500610900999 / 64000000000000 : ℝ) = (39500610900999 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39500610900999 / 32000000000000 : ℝ) ≤
            (2105802348358305921339 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3910153594579467 / 5000000000000000 : ℝ) ≤ Real.sqrt (39140610900999 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (39140610900999 / 64000000000000 : ℝ) ≤
      (7820307189158937 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (39140610900999 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau842 :
    Real.arctan (2606769063052979 / 7564923585141891 : ℝ) ≤
      (829609527283457739137 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau841 :
    Real.arctan (7820307189158937 / 10000000000000000 : ℝ) ≤
      (2 * (829609527283457739137 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12694770755425673 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7820307189158937 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7820307189158937 / 10000000000000000 : ℝ) /
                (1 + (12694770755425673 / 10000000000000000 : ℝ)) =
              (2606769063052979 / 7564923585141891 : ℝ)
            by
        norm_num];
        exact hau842)
  have hat1 :
    (Real.pi / 2 - (2 * (829609527283457739137 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7820307189158937 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7820307189158937 : ℝ) =
              (7820307189158937 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau841)
  have hz1 :
    (10000000000000000 / 7820307189158937 : ℝ) ≤
      1 / Real.sqrt (39140610900999 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7820307189158937 : ℝ) =
          1 / (7820307189158937 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1303384531526489 : ℝ) ≤
      (478058717204865695451 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (39140610900999 / 64000000000000 : ℝ) ≤
      (125000000000000 / 1303384531526489 : ℝ) := by
    rw [show
        (125000000000000 / 1303384531526489 : ℝ) =
          (3 / 40) / (3910153594579467 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (829609527283457739137 / 2500000000000000000000 : ℝ))) -
        6 * (478058717204865695451 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (39140610900999 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (39140610900999 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3910153594579467 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (829609527283457739137 / 2500000000000000000000 : ℝ))) -
          6 * (478058717204865695451 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (39140610900999 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (39140610900999 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (39140610900999 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_536 :
    ((4778768847802499834877 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4808269022174287691333 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1565435312978789 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3320568664278397156717 / 10000000000000000000000 : ℝ))) -
              6 * (238820853416915635233 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2450587719121 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2450587719121 / 4000000000000 : ℝ)) =
      Real.log (6450587719121 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2450587719121 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2473087719121 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4778768847802499834877 / 10000000000000000000000 : ℝ) ≤
      Real.log (6450587719121 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2473087719121 / 4000000000000 : ℝ) ≤
      (-(4808269022174287691333 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2473087719121 / 4000000000000 : ℝ) = (2473087719121 / 2000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2473087719121 / 2000000000000 : ℝ) ≤
            (2123202780825712308667 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1565435312978789 / 2000000000000000 : ℝ) ≤ Real.sqrt (2450587719121 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2450587719121 / 4000000000000 : ℝ) ≤ (1956794141223487 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2450587719121 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau844 :
    Real.arctan (7827176564893948 / 22699003621466725 : ℝ) ≤
      (3320568664278397156717 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau843 :
    Real.arctan (1956794141223487 / 2500000000000000 : ℝ) ≤
      (2 * (3320568664278397156717 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (507960144858669 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (1956794141223487 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1956794141223487 / 2500000000000000 : ℝ) /
                (1 + (507960144858669 / 400000000000000 : ℝ)) =
              (7827176564893948 / 22699003621466725 : ℝ)
            by
        norm_num];
        exact hau844)
  have hat1 :
    (Real.pi / 2 - (2 * (3320568664278397156717 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1956794141223487 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1956794141223487 : ℝ) =
              (1956794141223487 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau843)
  have hz1 :
    (2500000000000000 / 1956794141223487 : ℝ) ≤
      1 / Real.sqrt (2450587719121 / 4000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1956794141223487 : ℝ) = 1 / (1956794141223487 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1565435312978789 : ℝ) ≤
      (238820853416915635233 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2450587719121 / 4000000000000 : ℝ) ≤
      (150000000000000 / 1565435312978789 : ℝ) := by
    rw [show
        (150000000000000 / 1565435312978789 : ℝ) =
          (3 / 40) / (1565435312978789 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3320568664278397156717 / 10000000000000000000000 : ℝ))) -
        6 * (238820853416915635233 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2450587719121 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2450587719121 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1565435312978789 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3320568664278397156717 / 10000000000000000000000 : ℝ))) -
          6 * (238820853416915635233 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (2450587719121 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2450587719121 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2450587719121 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_537 :
    ((4785431970199179084243 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2395449407313415808313 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7834039917133371 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (664539186569865807171 / 2000000000000000000000 : ℝ))) -
              6 * (954451571688568381881 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (39278196110873 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (39278196110873 / 64000000000000 : ℝ)) =
      Real.log (103278196110873 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((39278196110873 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39638196110873 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4785431970199179084243 / 10000000000000000000000 : ℝ) ≤
      Real.log (103278196110873 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39638196110873 / 64000000000000 : ℝ) ≤
      (-(2395449407313415808313 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39638196110873 / 64000000000000 : ℝ) = (39638196110873 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39638196110873 / 32000000000000 : ℝ) ≤
            (1070286494186584191687 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7834039917133371 / 10000000000000000 : ℝ) ≤
      Real.sqrt (39278196110873 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (39278196110873 / 64000000000000 : ℝ) ≤ (3917019958566687 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (39278196110873 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau846 :
    Real.arctan (3917019958566687 / 11351617538533768 : ℝ) ≤
      (664539186569865807171 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau845 :
    Real.arctan (3917019958566687 / 5000000000000000 : ℝ) ≤
      (2 * (664539186569865807171 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (793952192316721 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (3917019958566687 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3917019958566687 / 5000000000000000 : ℝ) /
                (1 + (793952192316721 / 625000000000000 : ℝ)) =
              (3917019958566687 / 11351617538533768 : ℝ)
            by
        norm_num];
        exact hau846)
  have hat1 :
    (Real.pi / 2 - (2 * (664539186569865807171 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3917019958566687 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3917019958566687 : ℝ) =
              (3917019958566687 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau845)
  have hz1 :
    (5000000000000000 / 3917019958566687 : ℝ) ≤
      1 / Real.sqrt (39278196110873 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3917019958566687 : ℝ) = 1 / (3917019958566687 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2611346639044457 : ℝ) ≤
      (954451571688568381881 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (39278196110873 / 64000000000000 : ℝ) ≤
      (250000000000000 / 2611346639044457 : ℝ) := by
    rw [show
        (250000000000000 / 2611346639044457 : ℝ) =
          (3 / 40) / (7834039917133371 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (664539186569865807171 / 2000000000000000000000 : ℝ))) -
        6 * (954451571688568381881 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (39278196110873 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (39278196110873 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7834039917133371 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (664539186569865807171 / 2000000000000000000000 : ℝ))) -
          6 * (954451571688568381881 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (39278196110873 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (39278196110873 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (39278196110873 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_538 :
    ((2396045327915978534597 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2386779363589361089281 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3920448630847403 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3324819924122815790111 / 10000000000000000000000 : ℝ))) -
              6 * (953621899002678461567 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3934698871581 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3934698871581 / 6400000000000 : ℝ)) =
      Real.log (10334698871581 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3934698871581 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3970698871581 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2396045327915978534597 / 5000000000000000000000 : ℝ) ≤
      Real.log (10334698871581 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3970698871581 / 6400000000000 : ℝ) ≤
      (-(2386779363589361089281 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (3970698871581 / 6400000000000 : ℝ) = (3970698871581 / 3200000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3970698871581 / 3200000000000 : ℝ) ≤
            (1078956537910638910719 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3920448630847403 / 5000000000000000 : ℝ) ≤ Real.sqrt (3934698871581 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3934698871581 / 6400000000000 : ℝ) ≤ (7840897261694809 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3934698871581 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau848 :
    Real.arctan (7840897261694809 / 22707465123637094 : ℝ) ≤
      (3324819924122815790111 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau847 :
    Real.arctan (7840897261694809 / 10000000000000000 : ℝ) ≤
      (2 * (3324819924122815790111 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6353732561818547 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7840897261694809 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7840897261694809 / 10000000000000000 : ℝ) /
                (1 + (6353732561818547 / 5000000000000000 : ℝ)) =
              (7840897261694809 / 22707465123637094 : ℝ)
            by
        norm_num];
        exact hau848)
  have hat1 :
    (Real.pi / 2 - (2 * (3324819924122815790111 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7840897261694809 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7840897261694809 : ℝ) =
              (7840897261694809 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau847)
  have hz1 :
    (10000000000000000 / 7840897261694809 : ℝ) ≤
      1 / Real.sqrt (3934698871581 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7840897261694809 : ℝ) =
          1 / (7840897261694809 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3920448630847403 : ℝ) ≤
      (953621899002678461567 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3934698871581 / 6400000000000 : ℝ) ≤
      (375000000000000 / 3920448630847403 : ℝ) := by
    rw [show
        (375000000000000 / 3920448630847403 : ℝ) =
          (3 / 40) / (3920448630847403 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3324819924122815790111 / 10000000000000000000000 : ℝ))) -
        6 * (953621899002678461567 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3934698871581 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3934698871581 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3920448630847403 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3324819924122815790111 / 10000000000000000000000 : ℝ))) -
          6 * (953621899002678461567 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3934698871581 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3934698871581 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3934698871581 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_539 :
    ((2399372455302752849833 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1189062163888422939389 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7847748614326733 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3326940647335136480411 / 10000000000000000000000 : ℝ))) -
              6 * (119099298274718298781 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (39415781320747 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (39415781320747 / 64000000000000 : ℝ)) =
      Real.log (103415781320747 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((39415781320747 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39775781320747 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2399372455302752849833 / 5000000000000000000000 : ℝ) ≤
      Real.log (103415781320747 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39775781320747 / 64000000000000 : ℝ) ≤
      (-(1189062163888422939389 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39775781320747 / 64000000000000 : ℝ) = (39775781320747 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39775781320747 / 32000000000000 : ℝ) ≤
            (543805786861577060611 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7847748614326733 / 10000000000000000 : ℝ) ≤
      Real.sqrt (39415781320747 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (39415781320747 / 64000000000000 : ℝ) ≤ (490484288395421 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (39415781320747 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau850 :
    Real.arctan (7847748614326736 / 22711693762582041 : ℝ) ≤
      (3326940647335136480411 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau849 :
    Real.arctan (490484288395421 / 625000000000000 : ℝ) ≤
      (2 * (3326940647335136480411 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12711693762582041 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (490484288395421 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (490484288395421 / 625000000000000 : ℝ) /
                (1 + (12711693762582041 / 10000000000000000 : ℝ)) =
              (7847748614326736 / 22711693762582041 : ℝ)
            by
        norm_num];
        exact hau850)
  have hat1 :
    (Real.pi / 2 - (2 * (3326940647335136480411 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 490484288395421 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 490484288395421 : ℝ) =
              (490484288395421 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau849)
  have hz1 :
    (625000000000000 / 490484288395421 : ℝ) ≤
      1 / Real.sqrt (39415781320747 / 64000000000000 : ℝ) := by
    rw [show (625000000000000 / 490484288395421 : ℝ) = 1 / (490484288395421 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7847748614326733 : ℝ) ≤
      (119099298274718298781 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (39415781320747 / 64000000000000 : ℝ) ≤
      (750000000000000 / 7847748614326733 : ℝ) := by
    rw [show
        (750000000000000 / 7847748614326733 : ℝ) =
          (3 / 40) / (7847748614326733 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3326940647335136480411 / 10000000000000000000000 : ℝ))) -
        6 * (119099298274718298781 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (39415781320747 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (39415781320747 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7847748614326733 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3326940647335136480411 / 10000000000000000000000 : ℝ))) -
          6 * (119099298274718298781 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (39415781320747 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (39415781320747 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (39415781320747 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_540 :
    ((4805394740412717365303 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4738968496016046301109 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1570918798141791 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (83226452792072501471 / 250000000000000000000 : ℝ))) -
              6 * (475984511959300131801 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9871143481421 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9871143481421 / 16000000000000 : ℝ)) =
      Real.log (25871143481421 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9871143481421 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9961143481421 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4805394740412717365303 / 10000000000000000000000 : ℝ) ≤
      Real.log (25871143481421 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9961143481421 / 16000000000000 : ℝ) ≤
      (-(4738968496016046301109 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9961143481421 / 16000000000000 : ℝ) = (9961143481421 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9961143481421 / 8000000000000 : ℝ) ≤
            (2192503306983953698891 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1570918798141791 / 2000000000000000 : ℝ) ≤ Real.sqrt (9871143481421 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9871143481421 / 16000000000000 : ℝ) ≤ (3927296995354479 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9871143481421 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau852 :
    Real.arctan (3927296995354479 / 11357960497653340 : ℝ) ≤
      (83226452792072501471 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau851 :
    Real.arctan (3927296995354479 / 5000000000000000 : ℝ) ≤
      (2 * (83226452792072501471 / 250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (317898024882667 / 250000000000000 : ℝ) ≤
          Real.sqrt (1 + (3927296995354479 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3927296995354479 / 5000000000000000 : ℝ) /
                (1 + (317898024882667 / 250000000000000 : ℝ)) =
              (3927296995354479 / 11357960497653340 : ℝ)
            by
        norm_num];
        exact hau852)
  have hat1 :
    (Real.pi / 2 - (2 * (83226452792072501471 / 250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3927296995354479 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3927296995354479 : ℝ) =
              (3927296995354479 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau851)
  have hz1 :
    (5000000000000000 / 3927296995354479 : ℝ) ≤
      1 / Real.sqrt (9871143481421 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3927296995354479 : ℝ) = 1 / (3927296995354479 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 523639599380597 : ℝ) ≤
      (475984511959300131801 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9871143481421 / 16000000000000 : ℝ) ≤
      (50000000000000 / 523639599380597 : ℝ) := by
    rw [show
        (50000000000000 / 523639599380597 : ℝ) =
          (3 / 40) / (1570918798141791 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (83226452792072501471 / 250000000000000000000 : ℝ))) -
        6 * (475984511959300131801 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9871143481421 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9871143481421 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1570918798141791 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (83226452792072501471 / 250000000000000000000 : ℝ))) -
          6 * (475984511959300131801 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9871143481421 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9871143481421 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9871143481421 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
