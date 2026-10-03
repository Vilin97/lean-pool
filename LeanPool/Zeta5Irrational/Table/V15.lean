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

/-! # V15: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_181 :
    ((565756240004760742753 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20760370400176964455387 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1730616131954301 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3332169574449736592719 / 10000000000000000000000 : ℝ)) -
              6 * (213386950021971650621 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (3833641211111 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3833641211111 / 32000000000000 : ℝ)) =
      Real.log (35833641211111 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3833641211111 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4013641211111 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (565756240004760742753 / 5000000000000000000000 : ℝ) ≤
      Real.log (35833641211111 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4013641211111 / 32000000000000 : ℝ) ≤
      (-(20760370400176964455387 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4013641211111 / 32000000000000 : ℝ) = (4013641211111 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4013641211111 / 4000000000000 : ℝ) ≤
            (34045008823035544613 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1730616131954301 / 5000000000000000 : ℝ) ≤ Real.sqrt (3833641211111 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3833641211111 / 32000000000000 : ℝ) ≤ (692246452781721 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3833641211111 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau243 :
    Real.arctan (692246452781721 / 2000000000000000 : ℝ) ≤
      (3332169574449736592719 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3332169574449736592719 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 692246452781721 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 692246452781721 : ℝ) =
              (692246452781721 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau243)
  have hz1 :
    (2000000000000000 / 692246452781721 : ℝ) ≤
      1 / Real.sqrt (3833641211111 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 692246452781721 : ℝ) = 1 / (692246452781721 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 576872043984767 : ℝ) ≤
      (213386950021971650621 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3833641211111 / 32000000000000 : ℝ) ≤
      (125000000000000 / 576872043984767 : ℝ) := by
    rw [show
        (125000000000000 / 576872043984767 : ℝ) =
          (3 / 40) / (1730616131954301 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3332169574449736592719 / 10000000000000000000000 : ℝ)) -
        6 * (213386950021971650621 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3833641211111 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3833641211111 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1730616131954301 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3332169574449736592719 / 10000000000000000000000 : ℝ)) -
          6 * (213386950021971650621 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (3833641211111 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3833641211111 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3833641211111 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_182 :
    ((227553573578023514173 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4140932104806516067421 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3471339599085811 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (668238552174649568123 / 2000000000000000000000 : ℝ)) -
              6 * (265980315177075916949 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (1928031777949 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1928031777949 / 16000000000000 : ℝ)) =
      Real.log (17928031777949 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1928031777949 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2018031777949 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (227553573578023514173 / 2000000000000000000000 : ℝ) ≤
      Real.log (17928031777949 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2018031777949 / 16000000000000 : ℝ) ≤
      (-(4140932104806516067421 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2018031777949 / 16000000000000 : ℝ) = (2018031777949 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2018031777949 / 2000000000000 : ℝ) ≤
            (17950976993483932579 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3471339599085811 / 10000000000000000 : ℝ) ≤ Real.sqrt (1928031777949 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1928031777949 / 16000000000000 : ℝ) ≤ (1735669799542907 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1928031777949 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau244 :
    Real.arctan (1735669799542907 / 5000000000000000 : ℝ) ≤
      (668238552174649568123 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (668238552174649568123 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1735669799542907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1735669799542907 : ℝ) =
              (1735669799542907 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau244)
  have hz1 :
    (5000000000000000 / 1735669799542907 : ℝ) ≤
      1 / Real.sqrt (1928031777949 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1735669799542907 : ℝ) = 1 / (1735669799542907 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3471339599085811 : ℝ) ≤
      (265980315177075916949 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1928031777949 / 16000000000000 : ℝ) ≤
      (750000000000000 / 3471339599085811 : ℝ) := by
    rw [show
        (750000000000000 / 3471339599085811 : ℝ) =
          (3 / 40) / (3471339599085811 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (668238552174649568123 / 2000000000000000000000 : ℝ)) -
        6 * (265980315177075916949 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1928031777949 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1928031777949 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3471339599085811 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (668238552174649568123 / 2000000000000000000000 : ℝ)) -
          6 * (265980315177075916949 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (1928031777949 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1928031777949 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1928031777949 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_183 :
    ((115026691691253115783 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10297081645966272621029 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((139658659693411 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3359143938006206998433 / 10000000000000000000000 : ℝ)) -
              6 * (1057970113702477507409 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (121903382671 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (121903382671 / 1000000000000 : ℝ)) =
      Real.log (1121903382671 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((121903382671 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (127528382671 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (115026691691253115783 / 1000000000000000000000 : ℝ) ≤
      Real.log (1121903382671 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (127528382671 / 1000000000000 : ℝ) ≤
      (-(10297081645966272621029 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (127528382671 / 1000000000000 : ℝ) = (127528382671 / 125000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (127528382671 / 125000000000 : ℝ) ≤
            (100126058533727378971 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (139658659693411 / 400000000000000 : ℝ) ≤ Real.sqrt (121903382671 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (121903382671 / 1000000000000 : ℝ) ≤ (1745733246167639 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (121903382671 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau245 :
    Real.arctan (1745733246167639 / 5000000000000000 : ℝ) ≤
      (3359143938006206998433 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3359143938006206998433 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1745733246167639 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1745733246167639 : ℝ) =
              (1745733246167639 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau245)
  have hz1 :
    (5000000000000000 / 1745733246167639 : ℝ) ≤
      1 / Real.sqrt (121903382671 / 1000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1745733246167639 : ℝ) = 1 / (1745733246167639 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (30000000000000 / 139658659693411 : ℝ) ≤
      (1057970113702477507409 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (121903382671 / 1000000000000 : ℝ) ≤
      (30000000000000 / 139658659693411 : ℝ) := by
    rw [show
        (30000000000000 / 139658659693411 : ℝ) =
          (3 / 40) / (139658659693411 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3359143938006206998433 / 10000000000000000000000 : ℝ)) -
        6 * (1057970113702477507409 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (121903382671 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (121903382671 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((139658659693411 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3359143938006206998433 / 10000000000000000000000 : ℝ)) -
          6 * (1057970113702477507409 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (121903382671 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (121903382671 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (121903382671 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_184 :
    ((72671897675793028739 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10242436845908227152729 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((877869506319801 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1688484972162490177399 / 5000000000000000000000 : ℝ)) -
              6 * (263029436248314576797 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (1972876467523 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1972876467523 / 16000000000000 : ℝ)) =
      Real.log (17972876467523 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1972876467523 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2062876467523 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (72671897675793028739 / 625000000000000000000 : ℝ) ≤
      Real.log (17972876467523 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2062876467523 / 16000000000000 : ℝ) ≤
      (-(10242436845908227152729 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2062876467523 / 16000000000000 : ℝ) = (2062876467523 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2062876467523 / 2000000000000 : ℝ) ≤
            (154770858591772847271 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (877869506319801 / 2500000000000000 : ℝ) ≤ Real.sqrt (1972876467523 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1972876467523 / 16000000000000 : ℝ) ≤ (3511478025279207 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1972876467523 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau246 :
    Real.arctan (3511478025279207 / 10000000000000000 : ℝ) ≤
      (1688484972162490177399 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1688484972162490177399 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3511478025279207 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3511478025279207 : ℝ) =
              (3511478025279207 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau246)
  have hz1 :
    (10000000000000000 / 3511478025279207 : ℝ) ≤
      1 / Real.sqrt (1972876467523 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3511478025279207 : ℝ) =
          1 / (3511478025279207 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 292623168773267 : ℝ) ≤
      (263029436248314576797 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1972876467523 / 16000000000000 : ℝ) ≤
      (62500000000000 / 292623168773267 : ℝ) := by
    rw [show
        (62500000000000 / 292623168773267 : ℝ) =
          (3 / 40) / (877869506319801 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1688484972162490177399 / 5000000000000000000000 : ℝ)) -
        6 * (263029436248314576797 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1972876467523 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1972876467523 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((877869506319801 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1688484972162490177399 / 5000000000000000000000 : ℝ)) -
          6 * (263029436248314576797 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (1972876467523 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1972876467523 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1972876467523 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_185 :
    ((293804561124544004693 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(101883828061061805467 / 50000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3531376159082673 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (424334104594847274703 / 1250000000000000000000 : ℝ)) -
              6 * (1046361451427109468381 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (199529881231 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (199529881231 / 1600000000000 : ℝ)) =
      Real.log (1799529881231 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((199529881231 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (208529881231 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (293804561124544004693 / 2500000000000000000000 : ℝ) ≤
      Real.log (1799529881231 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (208529881231 / 1600000000000 : ℝ) ≤
      (-(101883828061061805467 / 50000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (208529881231 / 1600000000000 : ℝ) = (208529881231 / 200000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (208529881231 / 200000000000 : ℝ) ≤
            (2088248983938194533 / 50000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3531376159082673 / 10000000000000000 : ℝ) ≤ Real.sqrt (199529881231 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (199529881231 / 1600000000000 : ℝ) ≤ (882844039770669 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (199529881231 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau247 :
    Real.arctan (882844039770669 / 2500000000000000 : ℝ) ≤
      (424334104594847274703 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (424334104594847274703 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 882844039770669 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 882844039770669 : ℝ) =
              (882844039770669 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau247)
  have hz1 :
    (2500000000000000 / 882844039770669 : ℝ) ≤ 1 / Real.sqrt (199529881231 / 1600000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 882844039770669 : ℝ) = 1 / (882844039770669 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1177125386360891 : ℝ) ≤
      (1046361451427109468381 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (199529881231 / 1600000000000 : ℝ) ≤
      (250000000000000 / 1177125386360891 : ℝ) := by
    rw [show
        (250000000000000 / 1177125386360891 : ℝ) =
          (3 / 40) / (3531376159082673 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (424334104594847274703 / 1250000000000000000000 : ℝ)) -
        6 * (1046361451427109468381 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (199529881231 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (199529881231 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3531376159082673 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (424334104594847274703 / 1250000000000000000000 : ℝ)) -
          6 * (1046361451427109468381 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (199529881231 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (199529881231 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (199529881231 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_186 :
    ((74229412545702061359 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(158357920152138572839 / 78125000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1775581399982569 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (106632956741550105427 / 312500000000000000000 : ℝ)) -
              6 * (2081397264622508967207 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2017721157097 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2017721157097 / 16000000000000 : ℝ)) =
      Real.log (18017721157097 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2017721157097 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2107721157097 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (74229412545702061359 / 625000000000000000000 : ℝ) ≤
      Real.log (18017721157097 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2107721157097 / 16000000000000 : ℝ) ≤
      (-(158357920152138572839 / 78125000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2107721157097 / 16000000000000 : ℝ) = (2107721157097 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2107721157097 / 2000000000000 : ℝ) ≤
            (4098450230673927161 / 78125000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1775581399982569 / 5000000000000000 : ℝ) ≤ Real.sqrt (2017721157097 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2017721157097 / 16000000000000 : ℝ) ≤ (3551162799965141 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2017721157097 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau248 :
    Real.arctan (3551162799965141 / 10000000000000000 : ℝ) ≤
      (106632956741550105427 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (106632956741550105427 / 312500000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3551162799965141 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3551162799965141 : ℝ) =
              (3551162799965141 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau248)
  have hz1 :
    (10000000000000000 / 3551162799965141 : ℝ) ≤
      1 / Real.sqrt (2017721157097 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3551162799965141 : ℝ) =
          1 / (3551162799965141 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1775581399982569 : ℝ) ≤
      (2081397264622508967207 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2017721157097 / 16000000000000 : ℝ) ≤
      (375000000000000 / 1775581399982569 : ℝ) := by
    rw [show
        (375000000000000 / 1775581399982569 : ℝ) =
          (3 / 40) / (1775581399982569 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (106632956741550105427 / 312500000000000000000 : ℝ)) -
        6 * (2081397264622508967207 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2017721157097 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2017721157097 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1775581399982569 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (106632956741550105427 / 312500000000000000000 : ℝ)) -
          6 * (2081397264622508967207 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2017721157097 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2017721157097 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2017721157097 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_187 :
    ((1200107470129474167961 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5040998430578654879721 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((446354975166469 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (342971722732483462099 / 1000000000000000000000 : ℝ)) -
              6 * (82810142757838897227 / 400000000000000000000 : ℝ)))) ≤
      Vfield (510035875471 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (510035875471 / 4000000000000 : ℝ)) =
      Real.log (4510035875471 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((510035875471 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (532535875471 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1200107470129474167961 / 10000000000000000000000 : ℝ) ≤
      Real.log (4510035875471 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (532535875471 / 4000000000000 : ℝ) ≤
      (-(5040998430578654879721 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (532535875471 / 4000000000000 : ℝ) = (532535875471 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (532535875471 / 500000000000 : ℝ) ≤
            (157605421671345120279 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (446354975166469 / 1250000000000000 : ℝ) ≤ Real.sqrt (510035875471 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (510035875471 / 4000000000000 : ℝ) ≤ (714167960266351 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (510035875471 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau249 :
    Real.arctan (714167960266351 / 2000000000000000 : ℝ) ≤
      (342971722732483462099 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (342971722732483462099 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 714167960266351 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 714167960266351 : ℝ) =
              (714167960266351 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau249)
  have hz1 :
    (2000000000000000 / 714167960266351 : ℝ) ≤ 1 / Real.sqrt (510035875471 / 4000000000000 : ℝ) :=
  by
    rw [show
        (2000000000000000 / 714167960266351 : ℝ) = 1 / (714167960266351 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 446354975166469 : ℝ) ≤
      (82810142757838897227 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (510035875471 / 4000000000000 : ℝ) ≤
      (93750000000000 / 446354975166469 : ℝ) := by
    rw [show
        (93750000000000 / 446354975166469 : ℝ) =
          (3 / 40) / (446354975166469 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (342971722732483462099 / 1000000000000000000000 : ℝ)) -
        6 * (82810142757838897227 / 400000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (510035875471 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (510035875471 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((446354975166469 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (342971722732483462099 / 1000000000000000000000 : ℝ)) -
          6 * (82810142757838897227 / 400000000000000000000 : ℝ))) ≤
      Real.sqrt (510035875471 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (510035875471 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (510035875471 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_188 :
    ((612467451086576923913 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9977827430743743884387 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((360987204712473 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1732146236679985576439 / 5000000000000000000000 : ℝ)) -
              6 * (128030806236496645127 / 625000000000000000000 : ℝ)))) ≤
      Vfield (1042494095729 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1042494095729 / 8000000000000 : ℝ)) =
      Real.log (9042494095729 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1042494095729 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1087494095729 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (612467451086576923913 / 5000000000000000000000 : ℝ) ≤
      Real.log (9042494095729 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1087494095729 / 8000000000000 : ℝ) ≤
      (-(9977827430743743884387 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1087494095729 / 8000000000000 : ℝ) = (1087494095729 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1087494095729 / 1000000000000 : ℝ) ≤
            (419380273756256115613 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (360987204712473 / 1000000000000000 : ℝ) ≤ Real.sqrt (1042494095729 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1042494095729 / 8000000000000 : ℝ) ≤ (3609872047124733 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1042494095729 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau250 :
    Real.arctan (3609872047124733 / 10000000000000000 : ℝ) ≤
      (1732146236679985576439 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1732146236679985576439 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3609872047124733 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3609872047124733 : ℝ) =
              (3609872047124733 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau250)
  have hz1 :
    (10000000000000000 / 3609872047124733 : ℝ) ≤
      1 / Real.sqrt (1042494095729 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3609872047124733 : ℝ) =
          1 / (3609872047124733 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (25000000000000 / 120329068237491 : ℝ) ≤
      (128030806236496645127 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1042494095729 / 8000000000000 : ℝ) ≤
      (25000000000000 / 120329068237491 : ℝ) := by
    rw [show
        (25000000000000 / 120329068237491 : ℝ) =
          (3 / 40) / (360987204712473 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1732146236679985576439 / 5000000000000000000000 : ℝ)) -
        6 * (128030806236496645127 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1042494095729 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1042494095729 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((360987204712473 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1732146236679985576439 / 5000000000000000000000 : ℝ)) -
          6 * (128030806236496645127 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (1042494095729 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1042494095729 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1042494095729 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_189 :
    ((24994016934096835669 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(19751568072237638037033 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((145939469679453 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1749206566456722486477 / 5000000000000000000000 : ℝ)) -
              6 * (1013702202475916540091 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (266229110129 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (266229110129 / 2000000000000 : ℝ)) =
      Real.log (2266229110129 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((266229110129 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (277479110129 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (24994016934096835669 / 200000000000000000000 : ℝ) ≤
      Real.log (2266229110129 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (277479110129 / 2000000000000 : ℝ) ≤
      (-(19751568072237638037033 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (277479110129 / 2000000000000 : ℝ) = (277479110129 / 250000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (277479110129 / 250000000000 : ℝ) ≤
            (1042847336762361962967 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (145939469679453 / 400000000000000 : ℝ) ≤ Real.sqrt (266229110129 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (266229110129 / 2000000000000 : ℝ) ≤ (456060842748291 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (266229110129 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau251 :
    Real.arctan (456060842748291 / 1250000000000000 : ℝ) ≤
      (1749206566456722486477 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1749206566456722486477 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 456060842748291 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 456060842748291 : ℝ) =
              (456060842748291 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau251)
  have hz1 :
    (1250000000000000 / 456060842748291 : ℝ) ≤ 1 / Real.sqrt (266229110129 / 2000000000000 : ℝ) :=
  by
    rw [show
        (1250000000000000 / 456060842748291 : ℝ) = 1 / (456060842748291 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (10000000000000 / 48646489893151 : ℝ) ≤
      (1013702202475916540091 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (266229110129 / 2000000000000 : ℝ) ≤
      (10000000000000 / 48646489893151 : ℝ) := by
    rw [show
        (10000000000000 / 48646489893151 : ℝ) = (3 / 40) / (145939469679453 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1749206566456722486477 / 5000000000000000000000 : ℝ)) -
        6 * (1013702202475916540091 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (266229110129 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (266229110129 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((145939469679453 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1749206566456722486477 / 5000000000000000000000 : ℝ)) -
          6 * (1013702202475916540091 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (266229110129 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (266229110129 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (266229110129 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_190 :
    ((259809897242961142701 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1935548032090052720183 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((465564410925817 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3565345242591427109191 / 10000000000000000000000 : ℝ)) -
              6 * (397422127297066665873 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (110976113009 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (110976113009 / 800000000000 : ℝ)) =
      Real.log (910976113009 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((110976113009 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (115476113009 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (259809897242961142701 / 2000000000000000000000 : ℝ) ≤
      Real.log (910976113009 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (115476113009 / 800000000000 : ℝ) ≤
      (-(1935548032090052720183 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (115476113009 / 800000000000 : ℝ) = (115476113009 / 100000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115476113009 / 100000000000 : ℝ) ≤
            (143893508809947279817 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (465564410925817 / 1250000000000000 : ℝ) ≤ Real.sqrt (110976113009 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (110976113009 / 800000000000 : ℝ) ≤ (3724515287406539 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (110976113009 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau252 :
    Real.arctan (3724515287406539 / 10000000000000000 : ℝ) ≤
      (3565345242591427109191 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3565345242591427109191 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3724515287406539 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3724515287406539 : ℝ) =
              (3724515287406539 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau252)
  have hz1 :
    (10000000000000000 / 3724515287406539 : ℝ) ≤
      1 / Real.sqrt (110976113009 / 800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3724515287406539 : ℝ) =
          1 / (3724515287406539 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 465564410925817 : ℝ) ≤
      (397422127297066665873 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (110976113009 / 800000000000 : ℝ) ≤
      (93750000000000 / 465564410925817 : ℝ) := by
    rw [show
        (93750000000000 / 465564410925817 : ℝ) =
          (3 / 40) / (465564410925817 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3565345242591427109191 / 10000000000000000000000 : ℝ)) -
        6 * (397422127297066665873 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (110976113009 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (110976113009 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((465564410925817 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3565345242591427109191 / 10000000000000000000000 : ℝ)) -
          6 * (397422127297066665873 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (110976113009 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (110976113009 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (110976113009 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_191 :
    ((13481557922957465779 / 100000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4743621304204845889853 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3799022604012773 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3630616003248135794793 / 10000000000000000000000 : ℝ)) -
              6 * (1949127934440516860467 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (72162863729 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (72162863729 / 500000000000 : ℝ)) =
      Real.log (572162863729 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((72162863729 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (74975363729 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (13481557922957465779 / 100000000000000000000 : ℝ) ≤
      Real.log (572162863729 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (74975363729 / 500000000000 : ℝ) ≤
      (-(4743621304204845889853 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (74975363729 / 500000000000 : ℝ) = (74975363729 / 62500000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (74975363729 / 62500000000 : ℝ) ≤
            (454982548045154110147 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3799022604012773 / 10000000000000000 : ℝ) ≤ Real.sqrt (72162863729 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (72162863729 / 500000000000 : ℝ) ≤ (474877825501597 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (72162863729 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau253 :
    Real.arctan (474877825501597 / 1250000000000000 : ℝ) ≤
      (3630616003248135794793 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3630616003248135794793 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 474877825501597 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 474877825501597 : ℝ) =
              (474877825501597 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau253)
  have hz1 :
    (1250000000000000 / 474877825501597 : ℝ) ≤ 1 / Real.sqrt (72162863729 / 500000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 474877825501597 : ℝ) = 1 / (474877825501597 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3799022604012773 : ℝ) ≤
      (1949127934440516860467 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (72162863729 / 500000000000 : ℝ) ≤
      (750000000000000 / 3799022604012773 : ℝ) := by
    rw [show
        (750000000000000 / 3799022604012773 : ℝ) =
          (3 / 40) / (3799022604012773 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3630616003248135794793 / 10000000000000000000000 : ℝ)) -
        6 * (1949127934440516860467 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (72162863729 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (72162863729 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3799022604012773 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3630616003248135794793 / 10000000000000000000000 : ℝ)) -
          6 * (1949127934440516860467 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (72162863729 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (72162863729 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (72162863729 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_192 :
    ((1363649648793105799231 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18856849239285061292259 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1911152162703291 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1825472812071868163633 / 5000000000000000000000 : ℝ)) -
              6 * (968775768368206191403 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (4675203313927 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4675203313927 / 32000000000000 : ℝ)) =
      Real.log (36675203313927 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4675203313927 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4855203313927 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1363649648793105799231 / 10000000000000000000000 : ℝ) ≤
      Real.log (36675203313927 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4855203313927 / 32000000000000 : ℝ) ≤
      (-(18856849239285061292259 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4855203313927 / 32000000000000 : ℝ) = (4855203313927 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4855203313927 / 4000000000000 : ℝ) ≤
            (1937566169714938707741 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1911152162703291 / 5000000000000000 : ℝ) ≤ Real.sqrt (4675203313927 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4675203313927 / 32000000000000 : ℝ) ≤ (764460865081317 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4675203313927 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau254 :
    Real.arctan (764460865081317 / 2000000000000000 : ℝ) ≤
      (1825472812071868163633 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1825472812071868163633 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 764460865081317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 764460865081317 : ℝ) =
              (764460865081317 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau254)
  have hz1 :
    (2000000000000000 / 764460865081317 : ℝ) ≤
      1 / Real.sqrt (4675203313927 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 764460865081317 : ℝ) = 1 / (764460865081317 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 637050720901097 : ℝ) ≤
      (968775768368206191403 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4675203313927 / 32000000000000 : ℝ) ≤
      (125000000000000 / 637050720901097 : ℝ) := by
    rw [show
        (125000000000000 / 637050720901097 : ℝ) =
          (3 / 40) / (1911152162703291 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1825472812071868163633 / 5000000000000000000000 : ℝ)) -
        6 * (968775768368206191403 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4675203313927 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4675203313927 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1911152162703291 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1825472812071868163633 / 5000000000000000000000 : ℝ)) -
          6 * (968775768368206191403 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (4675203313927 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4675203313927 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4675203313927 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
