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

/-! # V19: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_229 :
    ((196312570291665255689 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8695478910589005680281 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4123762613683913 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1955649145612707344259 / 5000000000000000000000 : ℝ)) -
              6 * (224882887845839136873 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (10883467580171 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10883467580171 / 64000000000000 : ℝ)) =
      Real.log (74883467580171 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10883467580171 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11243467580171 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (196312570291665255689 / 1250000000000000000000 : ℝ) ≤
      Real.log (74883467580171 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11243467580171 / 64000000000000 : ℝ) ≤
      (-(8695478910589005680281 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (11243467580171 / 64000000000000 : ℝ) = (11243467580171 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11243467580171 / 8000000000000 : ℝ) ≤
            (1701728793910994319719 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4123762613683913 / 10000000000000000 : ℝ) ≤
      Real.sqrt (10883467580171 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10883467580171 / 64000000000000 : ℝ) ≤ (1030940653420979 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10883467580171 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau291 :
    Real.arctan (1030940653420979 / 2500000000000000 : ℝ) ≤
      (1955649145612707344259 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1955649145612707344259 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1030940653420979 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1030940653420979 : ℝ) =
              (1030940653420979 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau291)
  have hz1 :
    (2500000000000000 / 1030940653420979 : ℝ) ≤
      1 / Real.sqrt (10883467580171 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1030940653420979 : ℝ) = 1 / (1030940653420979 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4123762613683913 : ℝ) ≤
      (224882887845839136873 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10883467580171 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4123762613683913 : ℝ) := by
    rw [show
        (750000000000000 / 4123762613683913 : ℝ) =
          (3 / 40) / (4123762613683913 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1955649145612707344259 / 5000000000000000000000 : ℝ)) -
        6 * (224882887845839136873 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10883467580171 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10883467580171 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4123762613683913 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1955649145612707344259 / 5000000000000000000000 : ℝ)) -
          6 * (224882887845839136873 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (10883467580171 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10883467580171 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10883467580171 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_230 :
    ((197260017728728357033 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17340584442306510414111 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2067252820721749 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (39204764633408501653 / 100000000000000000000 : ℝ)) -
              6 * (112155517789191659431 / 625000000000000000000 : ℝ)))) ≤
      Vfield (5470123807721 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5470123807721 / 32000000000000 : ℝ)) =
      Real.log (37470123807721 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5470123807721 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5650123807721 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (197260017728728357033 / 1250000000000000000000 : ℝ) ≤
      Real.log (37470123807721 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5650123807721 / 32000000000000 : ℝ) ≤
      (-(17340584442306510414111 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5650123807721 / 32000000000000 : ℝ) = (5650123807721 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5650123807721 / 4000000000000 : ℝ) ≤
            (3453830966693489585889 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2067252820721749 / 5000000000000000 : ℝ) ≤ Real.sqrt (5470123807721 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5470123807721 / 32000000000000 : ℝ) ≤ (4134505641443501 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5470123807721 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau292 :
    Real.arctan (4134505641443501 / 10000000000000000 : ℝ) ≤
      (39204764633408501653 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (39204764633408501653 / 100000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4134505641443501 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4134505641443501 : ℝ) =
              (4134505641443501 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau292)
  have hz1 :
    (10000000000000000 / 4134505641443501 : ℝ) ≤
      1 / Real.sqrt (5470123807721 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4134505641443501 : ℝ) =
          1 / (4134505641443501 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2067252820721749 : ℝ) ≤
      (112155517789191659431 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5470123807721 / 32000000000000 : ℝ) ≤
      (375000000000000 / 2067252820721749 : ℝ) := by
    rw [show
        (375000000000000 / 2067252820721749 : ℝ) =
          (3 / 40) / (2067252820721749 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (39204764633408501653 / 100000000000000000000 : ℝ)) -
        6 * (112155517789191659431 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5470123807721 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5470123807721 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2067252820721749 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (39204764633408501653 / 100000000000000000000 : ℝ)) -
          6 * (112155517789191659431 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (5470123807721 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5470123807721 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5470123807721 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_231 :
    ((792826990337347588387 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8645231769943453544543 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2072610413478559 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (785924783077314604701 / 2000000000000000000000 : ℝ)) -
              6 * (447487048230703640181 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (10997027650713 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10997027650713 / 64000000000000 : ℝ)) =
      Real.log (74997027650713 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10997027650713 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11357027650713 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (792826990337347588387 / 5000000000000000000000 : ℝ) ≤
      Real.log (74997027650713 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11357027650713 / 64000000000000 : ℝ) ≤
      (-(8645231769943453544543 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (11357027650713 / 64000000000000 : ℝ) = (11357027650713 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11357027650713 / 8000000000000 : ℝ) ≤
            (1751975934556546455457 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2072610413478559 / 5000000000000000 : ℝ) ≤ Real.sqrt (10997027650713 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10997027650713 / 64000000000000 : ℝ) ≤
      (4145220826957121 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10997027650713 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau293 :
    Real.arctan (4145220826957121 / 10000000000000000 : ℝ) ≤
      (785924783077314604701 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (785924783077314604701 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4145220826957121 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4145220826957121 : ℝ) =
              (4145220826957121 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau293)
  have hz1 :
    (10000000000000000 / 4145220826957121 : ℝ) ≤
      1 / Real.sqrt (10997027650713 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4145220826957121 : ℝ) =
          1 / (4145220826957121 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2072610413478559 : ℝ) ≤
      (447487048230703640181 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10997027650713 / 64000000000000 : ℝ) ≤
      (375000000000000 / 2072610413478559 : ℝ) := by
    rw [show
        (375000000000000 / 2072610413478559 : ℝ) =
          (3 / 40) / (2072610413478559 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (785924783077314604701 / 2000000000000000000000 : ℝ)) -
        6 * (447487048230703640181 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10997027650713 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10997027650713 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2072610413478559 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (785924783077314604701 / 2000000000000000000000 : ℝ)) -
          6 * (447487048230703640181 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (10997027650713 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10997027650713 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10997027650713 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_232 :
    ((796611043778550434037 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4310148148915218457899 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((259744274098869 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1969370438785238650359 / 5000000000000000000000 : ℝ)) -
              6 * (892721195245301638437 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (345431490187 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (345431490187 / 2000000000000 : ℝ)) =
      Real.log (2345431490187 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((345431490187 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (356681490187 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (796611043778550434037 / 5000000000000000000000 : ℝ) ≤
      Real.log (2345431490187 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (356681490187 / 2000000000000 : ℝ) ≤
      (-(4310148148915218457899 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (356681490187 / 2000000000000 : ℝ) = (356681490187 / 250000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (356681490187 / 250000000000 : ℝ) ≤
            (888455703334781542101 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (259744274098869 / 625000000000000 : ℝ) ≤ Real.sqrt (345431490187 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (345431490187 / 2000000000000 : ℝ) ≤ (4155908385581907 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (345431490187 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau294 :
    Real.arctan (4155908385581907 / 10000000000000000 : ℝ) ≤
      (1969370438785238650359 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1969370438785238650359 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4155908385581907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4155908385581907 : ℝ) =
              (4155908385581907 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau294)
  have hz1 :
    (10000000000000000 / 4155908385581907 : ℝ) ≤
      1 / Real.sqrt (345431490187 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4155908385581907 : ℝ) =
          1 / (4155908385581907 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (15625000000000 / 86581424699623 : ℝ) ≤
      (892721195245301638437 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (345431490187 / 2000000000000 : ℝ) ≤
      (15625000000000 / 86581424699623 : ℝ) := by
    rw [show
        (15625000000000 / 86581424699623 : ℝ) = (3 / 40) / (259744274098869 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1969370438785238650359 / 5000000000000000000000 : ℝ)) -
        6 * (892721195245301638437 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (345431490187 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (345431490187 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((259744274098869 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1969370438785238650359 / 5000000000000000000000 : ℝ)) -
          6 * (892721195245301638437 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (345431490187 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (345431490187 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (345431490187 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_233 :
    ((804170570046356540339 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17141590695463957545947 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4177201469832627 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3956884238851918576391 / 10000000000000000000000 : ℝ)) -
              6 * (177653194295087677753 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (5583683878263 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5583683878263 / 32000000000000 : ℝ)) =
      Real.log (37583683878263 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5583683878263 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5763683878263 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (804170570046356540339 / 5000000000000000000000 : ℝ) ≤
      Real.log (37583683878263 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5763683878263 / 32000000000000 : ℝ) ≤
      (-(17141590695463957545947 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5763683878263 / 32000000000000 : ℝ) = (5763683878263 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5763683878263 / 4000000000000 : ℝ) ≤
            (3652824713536042454053 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4177201469832627 / 10000000000000000 : ℝ) ≤ Real.sqrt (5583683878263 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5583683878263 / 32000000000000 : ℝ) ≤ (417720146983263 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5583683878263 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau295 :
    Real.arctan (417720146983263 / 1000000000000000 : ℝ) ≤
      (3956884238851918576391 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3956884238851918576391 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 417720146983263 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 417720146983263 : ℝ) =
              (417720146983263 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau295)
  have hz1 :
    (1000000000000000 / 417720146983263 : ℝ) ≤
      1 / Real.sqrt (5583683878263 / 32000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 417720146983263 : ℝ) = 1 / (417720146983263 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1392400489944209 : ℝ) ≤
      (177653194295087677753 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5583683878263 / 32000000000000 : ℝ) ≤
      (250000000000000 / 1392400489944209 : ℝ) := by
    rw [show
        (250000000000000 / 1392400489944209 : ℝ) =
          (3 / 40) / (4177201469832627 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3956884238851918576391 / 10000000000000000000000 : ℝ)) -
        6 * (177653194295087677753 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5583683878263 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5583683878263 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4177201469832627 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3956884238851918576391 / 10000000000000000000000 : ℝ)) -
          6 * (177653194295087677753 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (5583683878263 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5583683878263 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5583683878263 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_234 :
    ((1623437368556860115687 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17043559332240260533931 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2099193281346059 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3974908332220430602867 / 10000000000000000000000 : ℝ)) -
              6 * (1767753594973346520647 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2820231956767 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2820231956767 / 16000000000000 : ℝ)) =
      Real.log (18820231956767 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2820231956767 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2910231956767 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1623437368556860115687 / 10000000000000000000000 : ℝ) ≤
      Real.log (18820231956767 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2910231956767 / 16000000000000 : ℝ) ≤
      (-(17043559332240260533931 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2910231956767 / 16000000000000 : ℝ) = (2910231956767 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2910231956767 / 2000000000000 : ℝ) ≤
            (3750856076759739466069 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2099193281346059 / 5000000000000000 : ℝ) ≤ Real.sqrt (2820231956767 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2820231956767 / 16000000000000 : ℝ) ≤ (4198386562692121 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2820231956767 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau296 :
    Real.arctan (4198386562692121 / 10000000000000000 : ℝ) ≤
      (3974908332220430602867 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3974908332220430602867 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4198386562692121 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4198386562692121 : ℝ) =
              (4198386562692121 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau296)
  have hz1 :
    (10000000000000000 / 4198386562692121 : ℝ) ≤
      1 / Real.sqrt (2820231956767 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4198386562692121 : ℝ) =
          1 / (4198386562692121 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2099193281346059 : ℝ) ≤
      (1767753594973346520647 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2820231956767 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2099193281346059 : ℝ) := by
    rw [show
        (375000000000000 / 2099193281346059 : ℝ) =
          (3 / 40) / (2099193281346059 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3974908332220430602867 / 10000000000000000000000 : ℝ)) -
        6 * (1767753594973346520647 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2820231956767 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2820231956767 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2099193281346059 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3974908332220430602867 / 10000000000000000000000 : ℝ)) -
          6 * (1767753594973346520647 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2820231956767 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2820231956767 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2820231956767 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_235 :
    ((8192554208785925893 / 50000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8473239830903755215511 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2109732645385169 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1996407449528079098729 / 5000000000000000000000 : ℝ)) -
              6 * (879552057096567979033 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1139448789761 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1139448789761 / 6400000000000 : ℝ)) =
      Real.log (7539448789761 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1139448789761 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1175448789761 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (8192554208785925893 / 50000000000000000000 : ℝ) ≤
      Real.log (7539448789761 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1175448789761 / 6400000000000 : ℝ) ≤
      (-(8473239830903755215511 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1175448789761 / 6400000000000 : ℝ) = (1175448789761 / 800000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1175448789761 / 800000000000 : ℝ) ≤
            (1923967873596244784489 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2109732645385169 / 5000000000000000 : ℝ) ≤ Real.sqrt (1139448789761 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1139448789761 / 6400000000000 : ℝ) ≤ (4219465290770341 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1139448789761 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau297 :
    Real.arctan (4219465290770341 / 10000000000000000 : ℝ) ≤
      (1996407449528079098729 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1996407449528079098729 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4219465290770341 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4219465290770341 : ℝ) =
              (4219465290770341 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau297)
  have hz1 :
    (10000000000000000 / 4219465290770341 : ℝ) ≤
      1 / Real.sqrt (1139448789761 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4219465290770341 : ℝ) =
          1 / (4219465290770341 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2109732645385169 : ℝ) ≤
      (879552057096567979033 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1139448789761 / 6400000000000 : ℝ) ≤
      (375000000000000 / 2109732645385169 : ℝ) := by
    rw [show
        (375000000000000 / 2109732645385169 : ℝ) =
          (3 / 40) / (2109732645385169 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1996407449528079098729 / 5000000000000000000000 : ℝ)) -
        6 * (879552057096567979033 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1139448789761 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1139448789761 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2109732645385169 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1996407449528079098729 / 5000000000000000000000 : ℝ)) -
          6 * (879552057096567979033 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1139448789761 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1139448789761 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1139448789761 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_236 :
    ((25836900440478381773 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2106291672941955151379 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4240439240248289 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4010605638583281302999 / 10000000000000000000000 : ℝ)) -
              6 * (54705636809765470191 / 312500000000000000000 : ℝ)))) ≤
      Vfield (1438505996019 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1438505996019 / 8000000000000 : ℝ)) =
      Real.log (9438505996019 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1438505996019 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1483505996019 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (25836900440478381773 / 156250000000000000000 : ℝ) ≤
      Real.log (9438505996019 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1483505996019 / 8000000000000 : ℝ) ≤
      (-(2106291672941955151379 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1483505996019 / 8000000000000 : ℝ) = (1483505996019 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1483505996019 / 1000000000000 : ℝ) ≤
            (493010253183044848621 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4240439240248289 / 10000000000000000 : ℝ) ≤ Real.sqrt (1438505996019 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1438505996019 / 8000000000000 : ℝ) ≤ (1060109810062073 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1438505996019 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau298 :
    Real.arctan (1060109810062073 / 2500000000000000 : ℝ) ≤
      (4010605638583281302999 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4010605638583281302999 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1060109810062073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1060109810062073 : ℝ) =
              (1060109810062073 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau298)
  have hz1 :
    (2500000000000000 / 1060109810062073 : ℝ) ≤
      1 / Real.sqrt (1438505996019 / 8000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1060109810062073 : ℝ) = 1 / (1060109810062073 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4240439240248289 : ℝ) ≤
      (54705636809765470191 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1438505996019 / 8000000000000 : ℝ) ≤
      (750000000000000 / 4240439240248289 : ℝ) := by
    rw [show
        (750000000000000 / 4240439240248289 : ℝ) =
          (3 / 40) / (4240439240248289 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4010605638583281302999 / 10000000000000000000000 : ℝ)) -
        6 * (54705636809765470191 / 312500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1438505996019 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1438505996019 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4240439240248289 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4010605638583281302999 / 10000000000000000000000 : ℝ)) -
          6 * (54705636809765470191 / 312500000000000000000 : ℝ))) ≤
      Real.sqrt (1438505996019 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1438505996019 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1438505996019 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_237 :
    ((1683595413202401175063 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8330385197728652168027 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2141039477139623 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4045846230365333599963 / 10000000000000000000000 : ℝ)) -
              6 * (86694908410619904871 / 500000000000000000000 : ℝ)))) ≤
      Vfield (2933792027309 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2933792027309 / 16000000000000 : ℝ)) =
      Real.log (18933792027309 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2933792027309 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3023792027309 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1683595413202401175063 / 10000000000000000000000 : ℝ) ≤
      Real.log (18933792027309 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3023792027309 / 16000000000000 : ℝ) ≤
      (-(8330385197728652168027 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3023792027309 / 16000000000000 : ℝ) = (3023792027309 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3023792027309 / 2000000000000 : ℝ) ≤
            (2066822506771347831973 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2141039477139623 / 5000000000000000 : ℝ) ≤ Real.sqrt (2933792027309 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2933792027309 / 16000000000000 : ℝ) ≤ (4282078954279249 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2933792027309 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau299 :
    Real.arctan (4282078954279249 / 10000000000000000 : ℝ) ≤
      (4045846230365333599963 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4045846230365333599963 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4282078954279249 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4282078954279249 : ℝ) =
              (4282078954279249 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau299)
  have hz1 :
    (10000000000000000 / 4282078954279249 : ℝ) ≤
      1 / Real.sqrt (2933792027309 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4282078954279249 : ℝ) =
          1 / (4282078954279249 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2141039477139623 : ℝ) ≤
      (86694908410619904871 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2933792027309 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2141039477139623 : ℝ) := by
    rw [show
        (375000000000000 / 2141039477139623 : ℝ) =
          (3 / 40) / (2141039477139623 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4045846230365333599963 / 10000000000000000000000 : ℝ)) -
        6 * (86694908410619904871 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2933792027309 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2933792027309 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2141039477139623 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4045846230365333599963 / 10000000000000000000000 : ℝ)) -
          6 * (86694908410619904871 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (2933792027309 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2933792027309 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2933792027309 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_238 :
    ((1713539265424779612481 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2059341758896377698357 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2161658818542197 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2040321455583755349747 / 5000000000000000000000 : ℝ)) -
              6 * (343536800730602077419 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (149528603129 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (149528603129 / 800000000000 : ℝ)) =
      Real.log (949528603129 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((149528603129 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (154028603129 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1713539265424779612481 / 10000000000000000000000 : ℝ) ≤
      Real.log (949528603129 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (154028603129 / 800000000000 : ℝ) ≤
      (-(2059341758896377698357 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (154028603129 / 800000000000 : ℝ) = (154028603129 / 100000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (154028603129 / 100000000000 : ℝ) ≤
            (539960167228622301643 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2161658818542197 / 5000000000000000 : ℝ) ≤ Real.sqrt (149528603129 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (149528603129 / 800000000000 : ℝ) ≤ (4323317637084397 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (149528603129 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau300 :
    Real.arctan (4323317637084397 / 10000000000000000 : ℝ) ≤
      (2040321455583755349747 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2040321455583755349747 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4323317637084397 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4323317637084397 : ℝ) =
              (4323317637084397 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau300)
  have hz1 :
    (10000000000000000 / 4323317637084397 : ℝ) ≤
      1 / Real.sqrt (149528603129 / 800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4323317637084397 : ℝ) =
          1 / (4323317637084397 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2161658818542197 : ℝ) ≤
      (343536800730602077419 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (149528603129 / 800000000000 : ℝ) ≤
      (375000000000000 / 2161658818542197 : ℝ) := by
    rw [show
        (375000000000000 / 2161658818542197 : ℝ) =
          (3 / 40) / (2161658818542197 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2040321455583755349747 / 5000000000000000000000 : ℝ)) -
        6 * (343536800730602077419 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (149528603129 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (149528603129 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2161658818542197 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2040321455583755349747 / 5000000000000000000000 : ℝ)) -
          6 * (343536800730602077419 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (149528603129 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (149528603129 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (149528603129 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_239 :
    ((871696860918730643327 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(16292095582403450641143 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2182083328585823 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4115007895609233887117 / 10000000000000000000000 : ℝ)) -
              6 * (1701916397919497671761 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3047352097851 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3047352097851 / 16000000000000 : ℝ)) =
      Real.log (19047352097851 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3047352097851 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3137352097851 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (871696860918730643327 / 5000000000000000000000 : ℝ) ≤
      Real.log (19047352097851 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3137352097851 / 16000000000000 : ℝ) ≤
      (-(16292095582403450641143 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3137352097851 / 16000000000000 : ℝ) = (3137352097851 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3137352097851 / 2000000000000 : ℝ) ≤
            (4502319826596549358857 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2182083328585823 / 5000000000000000 : ℝ) ≤ Real.sqrt (3047352097851 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3047352097851 / 16000000000000 : ℝ) ≤ (4364166657171649 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3047352097851 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau301 :
    Real.arctan (4364166657171649 / 10000000000000000 : ℝ) ≤
      (4115007895609233887117 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4115007895609233887117 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4364166657171649 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4364166657171649 : ℝ) =
              (4364166657171649 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau301)
  have hz1 :
    (10000000000000000 / 4364166657171649 : ℝ) ≤
      1 / Real.sqrt (3047352097851 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4364166657171649 : ℝ) =
          1 / (4364166657171649 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2182083328585823 : ℝ) ≤
      (1701916397919497671761 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3047352097851 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2182083328585823 : ℝ) := by
    rw [show
        (375000000000000 / 2182083328585823 : ℝ) =
          (3 / 40) / (2182083328585823 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4115007895609233887117 / 10000000000000000000000 : ℝ)) -
        6 * (1701916397919497671761 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3047352097851 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3047352097851 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2182083328585823 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4115007895609233887117 / 10000000000000000000000 : ℝ)) -
          6 * (1701916397919497671761 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3047352097851 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3047352097851 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3047352097851 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_240 :
    ((443289828656272310679 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4028183258387475971649 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4404636855861387 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2074476423521889182987 / 5000000000000000000000 : ℝ)) -
              6 * (421643805205669706173 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1552066066561 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1552066066561 / 8000000000000 : ℝ)) =
      Real.log (9552066066561 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1552066066561 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1597066066561 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (443289828656272310679 / 2500000000000000000000 : ℝ) ≤
      Real.log (9552066066561 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1597066066561 / 8000000000000 : ℝ) ≤
      (-(4028183258387475971649 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1597066066561 / 8000000000000 : ℝ) = (1597066066561 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1597066066561 / 1000000000000 : ℝ) ≤
            (1170420593862524028351 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4404636855861387 / 10000000000000000 : ℝ) ≤ Real.sqrt (1552066066561 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1552066066561 / 8000000000000 : ℝ) ≤ (440463685586139 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1552066066561 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau302 :
    Real.arctan (440463685586139 / 1000000000000000 : ℝ) ≤
      (2074476423521889182987 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2074476423521889182987 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 440463685586139 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 440463685586139 : ℝ) =
              (440463685586139 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau302)
  have hz1 :
    (1000000000000000 / 440463685586139 : ℝ) ≤
      1 / Real.sqrt (1552066066561 / 8000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 440463685586139 : ℝ) = 1 / (440463685586139 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1468212285287129 : ℝ) ≤
      (421643805205669706173 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1552066066561 / 8000000000000 : ℝ) ≤
      (250000000000000 / 1468212285287129 : ℝ) := by
    rw [show
        (250000000000000 / 1468212285287129 : ℝ) =
          (3 / 40) / (4404636855861387 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2074476423521889182987 / 5000000000000000000000 : ℝ)) -
        6 * (421643805205669706173 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1552066066561 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1552066066561 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4404636855861387 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2074476423521889182987 / 5000000000000000000000 : ℝ)) -
          6 * (421643805205669706173 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1552066066561 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1552066066561 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1552066066561 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
