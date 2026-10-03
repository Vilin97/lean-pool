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

/-! # V43: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_517 :
    ((452972286411765166689 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5471342198361810627931 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7569548156750547 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1619843380159431640001 / 5000000000000000000000 : ℝ))) -
              6 * (246897195377139917649 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (18335378975157 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18335378975157 / 32000000000000 : ℝ)) =
      Real.log (50335378975157 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18335378975157 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18515378975157 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (452972286411765166689 / 1000000000000000000000 : ℝ) ≤
      Real.log (50335378975157 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18515378975157 / 32000000000000 : ℝ) ≤
      (-(5471342198361810627931 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18515378975157 / 32000000000000 : ℝ) = (18515378975157 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18515378975157 / 16000000000000 : ℝ) ≤
            (1460129604638189372069 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7569548156750547 / 10000000000000000 : ℝ) ≤
      Real.sqrt (18335378975157 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18335378975157 / 32000000000000 : ℝ) ≤ (151390963135011 / 200000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18335378975157 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau806 :
    Real.arctan (2523182718916850 / 7513950769089891 : ℝ) ≤
      (1619843380159431640001 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau805 :
    Real.arctan (151390963135011 / 200000000000000 : ℝ) ≤
      (2 * (1619843380159431640001 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12541852307269673 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (151390963135011 / 200000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (151390963135011 / 200000000000000 : ℝ) /
                (1 + (12541852307269673 / 10000000000000000 : ℝ)) =
              (2523182718916850 / 7513950769089891 : ℝ)
            by
        norm_num];
        exact hau806)
  have hat1 :
    (Real.pi / 2 - (2 * (1619843380159431640001 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (200000000000000 / 151390963135011 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 151390963135011 : ℝ) =
              (151390963135011 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau805)
  have hz1 :
    (200000000000000 / 151390963135011 : ℝ) ≤
      1 / Real.sqrt (18335378975157 / 32000000000000 : ℝ) := by
    rw [show (200000000000000 / 151390963135011 : ℝ) = 1 / (151390963135011 / 200000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2523182718916849 : ℝ) ≤
      (246897195377139917649 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18335378975157 / 32000000000000 : ℝ) ≤
      (250000000000000 / 2523182718916849 : ℝ) := by
    rw [show
        (250000000000000 / 2523182718916849 : ℝ) =
          (3 / 40) / (7569548156750547 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1619843380159431640001 / 5000000000000000000000 : ℝ))) -
        6 * (246897195377139917649 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18335378975157 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18335378975157 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7569548156750547 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1619843380159431640001 / 5000000000000000000000 : ℝ))) -
          6 * (246897195377139917649 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (18335378975157 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18335378975157 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18335378975157 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_518 :
    ((4545581204063767592191 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5428288780241887976119 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3793010209705643 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3244918614347308492101 / 10000000000000000000000 : ℝ))) -
              6 * (492729102817023540833 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2301908232149 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2301908232149 / 4000000000000 : ℝ)) =
      Real.log (6301908232149 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2301908232149 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2324408232149 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4545581204063767592191 / 10000000000000000000000 : ℝ) ≤
      Real.log (6301908232149 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2324408232149 / 4000000000000 : ℝ) ≤
      (-(5428288780241887976119 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2324408232149 / 4000000000000 : ℝ) = (2324408232149 / 2000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2324408232149 / 2000000000000 : ℝ) ≤
            (1503183022758112023881 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3793010209705643 / 5000000000000000 : ℝ) ≤ Real.sqrt (2301908232149 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2301908232149 / 4000000000000 : ℝ) ≤ (7586020419411289 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2301908232149 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau808 :
    Real.arctan (7586020419411289 / 22551800898824240 : ℝ) ≤
      (3244918614347308492101 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau807 :
    Real.arctan (7586020419411289 / 10000000000000000 : ℝ) ≤
      (2 * (3244918614347308492101 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (156897511235303 / 125000000000000 : ℝ) ≤
          Real.sqrt (1 + (7586020419411289 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7586020419411289 / 10000000000000000 : ℝ) /
                (1 + (156897511235303 / 125000000000000 : ℝ)) =
              (7586020419411289 / 22551800898824240 : ℝ)
            by
        norm_num];
        exact hau808)
  have hat1 :
    (Real.pi / 2 - (2 * (3244918614347308492101 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7586020419411289 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7586020419411289 : ℝ) =
              (7586020419411289 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau807)
  have hz1 :
    (10000000000000000 / 7586020419411289 : ℝ) ≤
      1 / Real.sqrt (2301908232149 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7586020419411289 : ℝ) =
          1 / (7586020419411289 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3793010209705643 : ℝ) ≤
      (492729102817023540833 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2301908232149 / 4000000000000 : ℝ) ≤
      (375000000000000 / 3793010209705643 : ℝ) := by
    rw [show
        (375000000000000 / 3793010209705643 : ℝ) =
          (3 / 40) / (3793010209705643 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3244918614347308492101 / 10000000000000000000000 : ℝ))) -
        6 * (492729102817023540833 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2301908232149 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2301908232149 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3793010209705643 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3244918614347308492101 / 10000000000000000000000 : ℝ))) -
          6 * (492729102817023540833 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (2301908232149 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2301908232149 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2301908232149 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_519 :
    ((114035360878214065547 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1346354981867526213689 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1900614247915729 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3250130866753457043071 / 10000000000000000000000 : ℝ))) -
              6 * (245835339961437818473 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (18495152739227 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18495152739227 / 32000000000000 : ℝ)) =
      Real.log (50495152739227 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18495152739227 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18675152739227 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (114035360878214065547 / 250000000000000000000 : ℝ) ≤
      Real.log (50495152739227 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18675152739227 / 32000000000000 : ℝ) ≤
      (-(1346354981867526213689 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18675152739227 / 32000000000000 : ℝ) = (18675152739227 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18675152739227 / 16000000000000 : ℝ) ≤
            (386512968882473786311 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1900614247915729 / 2500000000000000 : ℝ) ≤ Real.sqrt (18495152739227 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18495152739227 / 32000000000000 : ℝ) ≤
      (7602456991662919 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18495152739227 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau810 :
    Real.arctan (7602456991662919 / 22561741611340537 : ℝ) ≤
      (3250130866753457043071 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau809 :
    Real.arctan (7602456991662919 / 10000000000000000 : ℝ) ≤
      (2 * (3250130866753457043071 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12561741611340537 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7602456991662919 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7602456991662919 / 10000000000000000 : ℝ) /
                (1 + (12561741611340537 / 10000000000000000 : ℝ)) =
              (7602456991662919 / 22561741611340537 : ℝ)
            by
        norm_num];
        exact hau810)
  have hat1 :
    (Real.pi / 2 - (2 * (3250130866753457043071 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7602456991662919 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7602456991662919 : ℝ) =
              (7602456991662919 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau809)
  have hz1 :
    (10000000000000000 / 7602456991662919 : ℝ) ≤
      1 / Real.sqrt (18495152739227 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7602456991662919 : ℝ) =
          1 / (7602456991662919 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1900614247915729 : ℝ) ≤
      (245835339961437818473 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18495152739227 / 32000000000000 : ℝ) ≤
      (187500000000000 / 1900614247915729 : ℝ) := by
    rw [show
        (187500000000000 / 1900614247915729 : ℝ) =
          (3 / 40) / (1900614247915729 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3250130866753457043071 / 10000000000000000000000 : ℝ))) -
        6 * (245835339961437818473 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18495152739227 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18495152739227 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1900614247915729 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3250130866753457043071 / 10000000000000000000000 : ℝ))) -
          6 * (245835339961437818473 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (18495152739227 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18495152739227 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18495152739227 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_520 :
    ((228861131834866065769 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5342734064375408869163 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7618858104495957 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1627661826322526439887 / 5000000000000000000000 : ℝ))) -
              6 * (245309524326254742311 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (9287519810631 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9287519810631 / 16000000000000 : ℝ)) =
      Real.log (25287519810631 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9287519810631 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9377519810631 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (228861131834866065769 / 500000000000000000000 : ℝ) ≤
      Real.log (25287519810631 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9377519810631 / 16000000000000 : ℝ) ≤
      (-(5342734064375408869163 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9377519810631 / 16000000000000 : ℝ) = (9377519810631 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9377519810631 / 8000000000000 : ℝ) ≤
            (1588737738624591130837 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7618858104495957 / 10000000000000000 : ℝ) ≤ Real.sqrt (9287519810631 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9287519810631 / 16000000000000 : ℝ) ≤ (190471452612399 / 250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9287519810631 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau812 :
    Real.arctan (7618858104495960 / 22571674463508977 : ℝ) ≤
      (1627661826322526439887 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau811 :
    Real.arctan (190471452612399 / 250000000000000 : ℝ) ≤
      (2 * (1627661826322526439887 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12571674463508977 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (190471452612399 / 250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (190471452612399 / 250000000000000 : ℝ) /
                (1 + (12571674463508977 / 10000000000000000 : ℝ)) =
              (7618858104495960 / 22571674463508977 : ℝ)
            by
        norm_num];
        exact hau812)
  have hat1 :
    (Real.pi / 2 - (2 * (1627661826322526439887 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (250000000000000 / 190471452612399 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 190471452612399 : ℝ) =
              (190471452612399 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hau811)
  have hz1 :
    (250000000000000 / 190471452612399 : ℝ) ≤
      1 / Real.sqrt (9287519810631 / 16000000000000 : ℝ) := by
    rw [show (250000000000000 / 190471452612399 : ℝ) = 1 / (190471452612399 / 250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2539619368165319 : ℝ) ≤
      (245309524326254742311 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9287519810631 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2539619368165319 : ℝ) := by
    rw [show
        (250000000000000 / 2539619368165319 : ℝ) =
          (3 / 40) / (7618858104495957 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1627661826322526439887 / 5000000000000000000000 : ℝ))) -
        6 * (245309524326254742311 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9287519810631 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9287519810631 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7618858104495957 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1627661826322526439887 / 5000000000000000000000 : ℝ))) -
          6 * (245309524326254742311 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (9287519810631 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9287519810631 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9287519810631 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_521 :
    ((4608764267010799293243 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(131447627616321705781 / 250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3825777431750391 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (816412839554078022283 / 2500000000000000000000 : ℝ))) -
              6 * (61066984094740587393 / 625000000000000000000 : ℝ)))) ≤
      Vfield (4683703346333 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4683703346333 / 8000000000000 : ℝ)) =
      Real.log (12683703346333 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4683703346333 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4728703346333 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4608764267010799293243 / 10000000000000000000000 : ℝ) ≤
      Real.log (12683703346333 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4728703346333 / 8000000000000 : ℝ) ≤
      (-(131447627616321705781 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4728703346333 / 8000000000000 : ℝ) = (4728703346333 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4728703346333 / 4000000000000 : ℝ) ≤
            (41839167458678294219 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3825777431750391 / 5000000000000000 : ℝ) ≤ Real.sqrt (4683703346333 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4683703346333 / 8000000000000 : ℝ) ≤ (1530310972700157 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4683703346333 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau814 :
    Real.arctan (510103657566719 / 1506101110746363 : ℝ) ≤
      (816412839554078022283 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau813 :
    Real.arctan (1530310972700157 / 2000000000000000 : ℝ) ≤
      (2 * (816412839554078022283 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2518303332239089 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1530310972700157 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1530310972700157 / 2000000000000000 : ℝ) /
                (1 + (2518303332239089 / 2000000000000000 : ℝ)) =
              (510103657566719 / 1506101110746363 : ℝ)
            by
        norm_num];
        exact hau814)
  have hat1 :
    (Real.pi / 2 - (2 * (816412839554078022283 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1530310972700157 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1530310972700157 : ℝ) =
              (1530310972700157 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau813)
  have hz1 :
    (2000000000000000 / 1530310972700157 : ℝ) ≤
      1 / Real.sqrt (4683703346333 / 8000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1530310972700157 : ℝ) = 1 / (1530310972700157 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1275259143916797 : ℝ) ≤
      (61066984094740587393 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4683703346333 / 8000000000000 : ℝ) ≤
      (125000000000000 / 1275259143916797 : ℝ) := by
    rw [show
        (125000000000000 / 1275259143916797 : ℝ) =
          (3 / 40) / (3825777431750391 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (816412839554078022283 / 2500000000000000000000 : ℝ))) -
        6 * (61066984094740587393 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4683703346333 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4683703346333 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3825777431750391 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (816412839554078022283 / 2500000000000000000000 : ℝ))) -
          6 * (61066984094740587393 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (4683703346333 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4683703346333 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4683703346333 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_522 :
    ((290012920163202756309 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(323361855717053871977 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7684112495394717 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3275902783813129556593 / 10000000000000000000000 : ℝ))) -
              6 * (486479009297971681703 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9447293574701 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9447293574701 / 16000000000000 : ℝ)) =
      Real.log (25447293574701 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9447293574701 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9537293574701 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (290012920163202756309 / 625000000000000000000 : ℝ) ≤
      Real.log (25447293574701 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9537293574701 / 16000000000000 : ℝ) ≤
      (-(323361855717053871977 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9537293574701 / 16000000000000 : ℝ) = (9537293574701 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9537293574701 / 8000000000000 : ℝ) ≤
            (109855131970446128023 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7684112495394717 / 10000000000000000 : ℝ) ≤ Real.sqrt (9447293574701 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9447293574701 / 16000000000000 : ℝ) ≤ (48025703096217 / 62500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9447293574701 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau816 :
    Real.arctan (452006617376160 / 1330078096466981 : ℝ) ≤
      (3275902783813129556593 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau815 :
    Real.arctan (48025703096217 / 62500000000000 : ℝ) ≤
      (2 * (3275902783813129556593 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12611327639938677 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (48025703096217 / 62500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (48025703096217 / 62500000000000 : ℝ) /
                (1 + (12611327639938677 / 10000000000000000 : ℝ)) =
              (452006617376160 / 1330078096466981 : ℝ)
            by
        norm_num];
        exact hau816)
  have hat1 :
    (Real.pi / 2 - (2 * (3275902783813129556593 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (62500000000000 / 48025703096217 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (62500000000000 / 48025703096217 : ℝ) =
              (48025703096217 / 62500000000000 : ℝ)
            by
        norm_num];
        exact hau815)
  have hz1 :
    (62500000000000 / 48025703096217 : ℝ) ≤ 1 / Real.sqrt (9447293574701 / 16000000000000 : ℝ) := by
    rw [show (62500000000000 / 48025703096217 : ℝ) = 1 / (48025703096217 / 62500000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2561370831798239 : ℝ) ≤
      (486479009297971681703 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9447293574701 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2561370831798239 : ℝ) := by
    rw [show
        (250000000000000 / 2561370831798239 : ℝ) =
          (3 / 40) / (7684112495394717 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3275902783813129556593 / 10000000000000000000000 : ℝ))) -
        6 * (486479009297971681703 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9447293574701 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9447293574701 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7684112495394717 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3275902783813129556593 / 10000000000000000000000 : ℝ))) -
          6 * (486479009297971681703 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9447293574701 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9447293574701 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9447293574701 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_523 :
    ((467155062520418752421 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(19884280940523666413 / 39062500000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((308661310447811 / 400000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (410759870046985860257 / 1250000000000000000000 : ℝ))) -
              6 * (121111977243712197883 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (297724389273 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (297724389273 / 500000000000 : ℝ)) =
      Real.log (797724389273 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((297724389273 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (300536889273 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (467155062520418752421 / 1000000000000000000000 : ℝ) ≤
      Real.log (797724389273 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (300536889273 / 500000000000 : ℝ) ≤
      (-(19884280940523666413 / 39062500000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (300536889273 / 500000000000 : ℝ) = (300536889273 / 250000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (300536889273 / 250000000000 : ℝ) ≤
            (7191780789945083587 / 39062500000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (308661310447811 / 400000000000000 : ℝ) ≤ Real.sqrt (297724389273 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (297724389273 / 500000000000 : ℝ) ≤ (3858266380597639 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (297724389273 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau818 :
    Real.arctan (3858266380597639 / 11315553773316319 : ℝ) ≤
      (410759870046985860257 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau817 :
    Real.arctan (3858266380597639 / 5000000000000000 : ℝ) ≤
      (2 * (410759870046985860257 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6315553773316319 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3858266380597639 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3858266380597639 / 5000000000000000 : ℝ) /
                (1 + (6315553773316319 / 5000000000000000 : ℝ)) =
              (3858266380597639 / 11315553773316319 : ℝ)
            by
        norm_num];
        exact hau818)
  have hat1 :
    (Real.pi / 2 - (2 * (410759870046985860257 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3858266380597639 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3858266380597639 : ℝ) =
              (3858266380597639 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau817)
  have hz1 :
    (5000000000000000 / 3858266380597639 : ℝ) ≤ 1 / Real.sqrt (297724389273 / 500000000000 : ℝ) :=
  by
    rw [show
        (5000000000000000 / 3858266380597639 : ℝ) = 1 / (3858266380597639 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (30000000000000 / 308661310447811 : ℝ) ≤
      (121111977243712197883 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (297724389273 / 500000000000 : ℝ) ≤
      (30000000000000 / 308661310447811 : ℝ) := by
    rw [show
        (30000000000000 / 308661310447811 : ℝ) =
          (3 / 40) / (308661310447811 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (410759870046985860257 / 1250000000000000000000 : ℝ))) -
        6 * (121111977243712197883 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (297724389273 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (297724389273 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((308661310447811 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (410759870046985860257 / 1250000000000000000000 : ℝ))) -
          6 * (121111977243712197883 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (297724389273 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (297724389273 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (297724389273 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_524 :
    ((4685015939116695900419 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5054674252401897476843 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3865224920526233 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1645218759627469874719 / 5000000000000000000000 : ℝ))) -
              6 * (193432477556515180871 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (19123153518409 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19123153518409 / 32000000000000 : ℝ)) =
      Real.log (51123153518409 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19123153518409 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19303153518409 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4685015939116695900419 / 10000000000000000000000 : ℝ) ≤
      Real.log (51123153518409 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19303153518409 / 32000000000000 : ℝ) ≤
      (-(5054674252401897476843 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19303153518409 / 32000000000000 : ℝ) = (19303153518409 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19303153518409 / 16000000000000 : ℝ) ≤
            (1876797550598102523157 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3865224920526233 / 5000000000000000 : ℝ) ≤ Real.sqrt (19123153518409 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19123153518409 / 32000000000000 : ℝ) ≤
      (7730449841052469 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19123153518409 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau820 :
    Real.arctan (7730449841052469 / 22639614501440624 : ℝ) ≤
      (1645218759627469874719 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau819 :
    Real.arctan (7730449841052469 / 10000000000000000 : ℝ) ≤
      (2 * (1645218759627469874719 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (789975906340039 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (7730449841052469 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7730449841052469 / 10000000000000000 : ℝ) /
                (1 + (789975906340039 / 625000000000000 : ℝ)) =
              (7730449841052469 / 22639614501440624 : ℝ)
            by
        norm_num];
        exact hau820)
  have hat1 :
    (Real.pi / 2 - (2 * (1645218759627469874719 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7730449841052469 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7730449841052469 : ℝ) =
              (7730449841052469 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau819)
  have hz1 :
    (10000000000000000 / 7730449841052469 : ℝ) ≤
      1 / Real.sqrt (19123153518409 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7730449841052469 : ℝ) =
          1 / (7730449841052469 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3865224920526233 : ℝ) ≤
      (193432477556515180871 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19123153518409 / 32000000000000 : ℝ) ≤
      (375000000000000 / 3865224920526233 : ℝ) := by
    rw [show
        (375000000000000 / 3865224920526233 : ℝ) =
          (3 / 40) / (3865224920526233 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1645218759627469874719 / 5000000000000000000000 : ℝ))) -
        6 * (193432477556515180871 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19123153518409 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19123153518409 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3865224920526233 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1645218759627469874719 / 5000000000000000000000 : ℝ))) -
          6 * (193432477556515180871 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (19123153518409 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19123153518409 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19123153518409 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_525 :
    ((4698463145940359342123 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5019099591638264099907 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7744341911063601 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3294782395019543481039 / 10000000000000000000000 : ℝ))) -
              6 * (120679778530763911613 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (9595973061673 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9595973061673 / 16000000000000 : ℝ)) =
      Real.log (25595973061673 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9595973061673 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9685973061673 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4698463145940359342123 / 10000000000000000000000 : ℝ) ≤
      Real.log (25595973061673 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9685973061673 / 16000000000000 : ℝ) ≤
      (-(5019099591638264099907 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9685973061673 / 16000000000000 : ℝ) = (9685973061673 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9685973061673 / 8000000000000 : ℝ) ≤
            (1912372211361735900093 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7744341911063601 / 10000000000000000 : ℝ) ≤ Real.sqrt (9595973061673 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9595973061673 / 16000000000000 : ℝ) ≤ (1936085477765901 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9595973061673 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau822 :
    Real.arctan (7744341911063604 / 22648115734584983 : ℝ) ≤
      (3294782395019543481039 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau821 :
    Real.arctan (1936085477765901 / 2500000000000000 : ℝ) ≤
      (2 * (3294782395019543481039 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12648115734584983 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1936085477765901 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1936085477765901 / 2500000000000000 : ℝ) /
                (1 + (12648115734584983 / 10000000000000000 : ℝ)) =
              (7744341911063604 / 22648115734584983 : ℝ)
            by
        norm_num];
        exact hau822)
  have hat1 :
    (Real.pi / 2 - (2 * (3294782395019543481039 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1936085477765901 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1936085477765901 : ℝ) =
              (1936085477765901 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau821)
  have hz1 :
    (2500000000000000 / 1936085477765901 : ℝ) ≤
      1 / Real.sqrt (9595973061673 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1936085477765901 : ℝ) = 1 / (1936085477765901 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2581447303687867 : ℝ) ≤
      (120679778530763911613 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9595973061673 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2581447303687867 : ℝ) := by
    rw [show
        (250000000000000 / 2581447303687867 : ℝ) =
          (3 / 40) / (7744341911063601 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3294782395019543481039 / 10000000000000000000000 : ℝ))) -
        6 * (120679778530763911613 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9595973061673 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9595973061673 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7744341911063601 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3294782395019543481039 / 10000000000000000000000 : ℝ))) -
          6 * (120679778530763911613 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (9595973061673 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9595973061673 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9595973061673 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_526 :
    ((2355946147153874507959 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(155739094938564335577 / 312500000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3879104552789353 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3299113666383077039093 / 10000000000000000000000 : ℝ))) -
              6 * (481861628499394707899 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (19260738728283 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19260738728283 / 32000000000000 : ℝ)) =
      Real.log (51260738728283 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19260738728283 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19440738728283 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2355946147153874507959 / 5000000000000000000000 : ℝ) ≤
      Real.log (51260738728283 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19440738728283 / 32000000000000 : ℝ) ≤
      (-(155739094938564335577 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19440738728283 / 32000000000000 : ℝ) = (19440738728283 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19440738728283 / 16000000000000 : ℝ) ≤
            (60869398905185664423 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3879104552789353 / 5000000000000000 : ℝ) ≤ Real.sqrt (19260738728283 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19260738728283 / 32000000000000 : ℝ) ≤
      (7758209105578709 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19260738728283 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau824 :
    Real.arctan (7758209105578709 / 22656611257595153 : ℝ) ≤
      (3299113666383077039093 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau823 :
    Real.arctan (7758209105578709 / 10000000000000000 : ℝ) ≤
      (2 * (3299113666383077039093 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12656611257595153 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7758209105578709 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7758209105578709 / 10000000000000000 : ℝ) /
                (1 + (12656611257595153 / 10000000000000000 : ℝ)) =
              (7758209105578709 / 22656611257595153 : ℝ)
            by
        norm_num];
        exact hau824)
  have hat1 :
    (Real.pi / 2 - (2 * (3299113666383077039093 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7758209105578709 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7758209105578709 : ℝ) =
              (7758209105578709 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau823)
  have hz1 :
    (10000000000000000 / 7758209105578709 : ℝ) ≤
      1 / Real.sqrt (19260738728283 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7758209105578709 : ℝ) =
          1 / (7758209105578709 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3879104552789353 : ℝ) ≤
      (481861628499394707899 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19260738728283 / 32000000000000 : ℝ) ≤
      (375000000000000 / 3879104552789353 : ℝ) := by
    rw [show
        (375000000000000 / 3879104552789353 : ℝ) =
          (3 / 40) / (3879104552789353 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3299113666383077039093 / 10000000000000000000000 : ℝ))) -
        6 * (481861628499394707899 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19260738728283 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19260738728283 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3879104552789353 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3299113666383077039093 / 10000000000000000000000 : ℝ))) -
          6 * (481861628499394707899 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (19260738728283 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19260738728283 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19260738728283 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_527 :
    ((589825013964311084409 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4965973772639253023391 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((776513341618149 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1650637112411661779237 / 5000000000000000000000 : ℝ))) -
              6 * (481434595765630853183 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (38590270061503 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38590270061503 / 64000000000000 : ℝ)) =
      Real.log (102590270061503 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38590270061503 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (38950270061503 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (589825013964311084409 / 1250000000000000000000 : ℝ) ≤
      Real.log (102590270061503 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (38950270061503 / 64000000000000 : ℝ) ≤
      (-(4965973772639253023391 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (38950270061503 / 64000000000000 : ℝ) = (38950270061503 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38950270061503 / 32000000000000 : ℝ) ≤
            (1965498030360746976609 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (776513341618149 / 1000000000000000 : ℝ) ≤ Real.sqrt (38590270061503 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38590270061503 / 64000000000000 : ℝ) ≤
      (7765133416181493 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38590270061503 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau826 :
    Real.arctan (7765133416181493 / 22660856881392287 : ℝ) ≤
      (1650637112411661779237 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau825 :
    Real.arctan (7765133416181493 / 10000000000000000 : ℝ) ≤
      (2 * (1650637112411661779237 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12660856881392287 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7765133416181493 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7765133416181493 / 10000000000000000 : ℝ) /
                (1 + (12660856881392287 / 10000000000000000 : ℝ)) =
              (7765133416181493 / 22660856881392287 : ℝ)
            by
        norm_num];
        exact hau826)
  have hat1 :
    (Real.pi / 2 - (2 * (1650637112411661779237 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7765133416181493 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7765133416181493 : ℝ) =
              (7765133416181493 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau825)
  have hz1 :
    (10000000000000000 / 7765133416181493 : ℝ) ≤
      1 / Real.sqrt (38590270061503 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7765133416181493 : ℝ) =
          1 / (7765133416181493 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (25000000000000 / 258837780539383 : ℝ) ≤
      (481434595765630853183 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38590270061503 / 64000000000000 : ℝ) ≤
      (25000000000000 / 258837780539383 : ℝ) := by
    rw [show
        (25000000000000 / 258837780539383 : ℝ) =
          (3 / 40) / (776513341618149 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1650637112411661779237 / 5000000000000000000000 : ℝ))) -
        6 * (481434595765630853183 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38590270061503 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38590270061503 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((776513341618149 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1650637112411661779237 / 5000000000000000000000 : ℝ))) -
          6 * (481434595765630853183 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (38590270061503 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38590270061503 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38590270061503 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_528 :
    ((4725303432655770558119 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2474163850341135916233 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3886025778874623 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (20646446321052335661 / 62500000000000000000 : ℝ))) -
              6 * (48100869635968825743 / 500000000000000000000 : ℝ)))) ≤
      Vfield (966476566661 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (966476566661 / 1600000000000 : ℝ)) =
      Real.log (2566476566661 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((966476566661 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (975476566661 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4725303432655770558119 / 10000000000000000000000 : ℝ) ≤
      Real.log (2566476566661 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (975476566661 / 1600000000000 : ℝ) ≤
      (-(2474163850341135916233 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (975476566661 / 1600000000000 : ℝ) = (975476566661 / 800000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (975476566661 / 800000000000 : ℝ) ≤
            (991572051158864083767 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3886025778874623 / 5000000000000000 : ℝ) ≤ Real.sqrt (966476566661 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (966476566661 / 1600000000000 : ℝ) ≤ (7772051557749249 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (966476566661 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau828 :
    Real.arctan (2590683852583083 / 7555033693987300 : ℝ) ≤
      (20646446321052335661 / 62500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau827 :
    Real.arctan (7772051557749249 / 10000000000000000 : ℝ) ≤
      (2 * (20646446321052335661 / 62500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (126651010819619 / 100000000000000 : ℝ) ≤
          Real.sqrt (1 + (7772051557749249 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7772051557749249 / 10000000000000000 : ℝ) /
                (1 + (126651010819619 / 100000000000000 : ℝ)) =
              (2590683852583083 / 7555033693987300 : ℝ)
            by
        norm_num];
        exact hau828)
  have hat1 :
    (Real.pi / 2 - (2 * (20646446321052335661 / 62500000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7772051557749249 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7772051557749249 : ℝ) =
              (7772051557749249 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau827)
  have hz1 :
    (10000000000000000 / 7772051557749249 : ℝ) ≤
      1 / Real.sqrt (966476566661 / 1600000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7772051557749249 : ℝ) =
          1 / (7772051557749249 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1295341926291541 : ℝ) ≤
      (48100869635968825743 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (966476566661 / 1600000000000 : ℝ) ≤
      (125000000000000 / 1295341926291541 : ℝ) := by
    rw [show
        (125000000000000 / 1295341926291541 : ℝ) =
          (3 / 40) / (3886025778874623 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (20646446321052335661 / 62500000000000000000 : ℝ))) -
        6 * (48100869635968825743 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (966476566661 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (966476566661 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3886025778874623 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (20646446321052335661 / 62500000000000000000 : ℝ))) -
          6 * (48100869635968825743 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (966476566661 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (966476566661 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (966476566661 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
