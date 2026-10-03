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

/-! # V53: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_637 :
    ((1381932097217859613867 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(370162538946138480059 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2147768782037017 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (443598587162207701421 / 1250000000000000000000 : ℝ))) -
              6 * (217697824813350455459 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (4723620598879 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4723620598879 / 6400000000000 : ℝ)) =
      Real.log (11123620598879 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4723620598879 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4759620598879 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1381932097217859613867 / 2500000000000000000000 : ℝ) ≤
      Real.log (11123620598879 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4759620598879 / 6400000000000 : ℝ) ≤
      (-(370162538946138480059 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4759620598879 / 6400000000000 : ℝ) = (4759620598879 / 3200000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4759620598879 / 3200000000000 : ℝ) ≤
            (496271436428861519941 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2147768782037017 / 2500000000000000 : ℝ) ≤ Real.sqrt (4723620598879 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4723620598879 / 6400000000000 : ℝ) ≤ (8591075128148071 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4723620598879 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1046 :
    Real.arctan (8591075128148071 / 23183572044688206 : ℝ) ≤
      (443598587162207701421 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1045 :
    Real.arctan (8591075128148071 / 10000000000000000 : ℝ) ≤
      (2 * (443598587162207701421 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6591786022344103 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8591075128148071 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8591075128148071 / 10000000000000000 : ℝ) /
                (1 + (6591786022344103 / 5000000000000000 : ℝ)) =
              (8591075128148071 / 23183572044688206 : ℝ)
            by
        norm_num];
        exact hau1046)
  have hat1 :
    (Real.pi / 2 - (2 * (443598587162207701421 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8591075128148071 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8591075128148071 : ℝ) =
              (8591075128148071 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1045)
  have hz1 :
    (10000000000000000 / 8591075128148071 : ℝ) ≤
      1 / Real.sqrt (4723620598879 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8591075128148071 : ℝ) =
          1 / (8591075128148071 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2147768782037017 : ℝ) ≤
      (217697824813350455459 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4723620598879 / 6400000000000 : ℝ) ≤
      (187500000000000 / 2147768782037017 : ℝ) := by
    rw [show
        (187500000000000 / 2147768782037017 : ℝ) =
          (3 / 40) / (2147768782037017 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (443598587162207701421 / 1250000000000000000000 : ℝ))) -
        6 * (217697824813350455459 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4723620598879 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4723620598879 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2147768782037017 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (443598587162207701421 / 1250000000000000000000 : ℝ))) -
          6 * (217697824813350455459 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (4723620598879 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4723620598879 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4723620598879 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_638 :
    ((691650816020377922461 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(147425107002328637843 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8596616287992327 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ))) -
              6 * (870232839768089163139 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2956072464119 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2956072464119 / 4000000000000 : ℝ)) =
      Real.log (6956072464119 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2956072464119 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2978572464119 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (691650816020377922461 / 1250000000000000000000 : ℝ) ≤
      Real.log (6956072464119 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2978572464119 / 4000000000000 : ℝ) ≤
      (-(147425107002328637843 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2978572464119 / 4000000000000 : ℝ) = (2978572464119 / 2000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2978572464119 / 2000000000000 : ℝ) ≤
            (199148483147671362157 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8596616287992327 / 10000000000000000 : ℝ) ≤ Real.sqrt (2956072464119 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2956072464119 / 4000000000000 : ℝ) ≤ (859661628799233 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2956072464119 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1048 :
    Real.arctan (4298308143996165 / 11593591805741674 : ℝ) ≤
      (3550382320117678762279 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1047 :
    Real.arctan (859661628799233 / 1000000000000000 : ℝ) ≤
      (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3296795902870837 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (859661628799233 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (859661628799233 / 1000000000000000 : ℝ) /
                (1 + (3296795902870837 / 2500000000000000 : ℝ)) =
              (4298308143996165 / 11593591805741674 : ℝ)
            by
        norm_num];
        exact hau1048)
  have hat1 :
    (Real.pi / 2 - (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 859661628799233 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 859661628799233 : ℝ) =
              (859661628799233 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau1047)
  have hz1 :
    (1000000000000000 / 859661628799233 : ℝ) ≤
      1 / Real.sqrt (2956072464119 / 4000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 859661628799233 : ℝ) = 1 / (859661628799233 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2865538762664109 : ℝ) ≤
      (870232839768089163139 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2956072464119 / 4000000000000 : ℝ) ≤
      (250000000000000 / 2865538762664109 : ℝ) := by
    rw [show
        (250000000000000 / 2865538762664109 : ℝ) =
          (3 / 40) / (8596616287992327 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ))) -
        6 * (870232839768089163139 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2956072464119 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2956072464119 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8596616287992327 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ))) -
          6 * (870232839768089163139 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2956072464119 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2956072464119 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2956072464119 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_639 :
    ((1384670417024153405141 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(36696504086374459829 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8602153878446119 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ))) -
              6 * (21741886334314884711 / 250000000000000000000 : ℝ)))) ≤
      Vfield (23679056431509 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23679056431509 / 32000000000000 : ℝ)) =
      Real.log (55679056431509 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23679056431509 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23859056431509 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1384670417024153405141 / 2500000000000000000000 : ℝ) ≤
      Real.log (55679056431509 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23859056431509 / 32000000000000 : ℝ) ≤
      (-(36696504086374459829 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23859056431509 / 32000000000000 : ℝ) = (23859056431509 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23859056431509 / 16000000000000 : ℝ) ≤
            (49946893451125540171 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8602153878446119 / 10000000000000000 : ℝ) ≤
      Real.sqrt (23679056431509 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23679056431509 / 32000000000000 : ℝ) ≤ (4301076939223061 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23679056431509 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1050 :
    Real.arctan (4301076939223061 / 11595397094725715 : ℝ) ≤
      (3551974044421646939057 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1049 :
    Real.arctan (4301076939223061 / 5000000000000000 : ℝ) ≤
      (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1319079418945143 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4301076939223061 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4301076939223061 / 5000000000000000 : ℝ) /
                (1 + (1319079418945143 / 1000000000000000 : ℝ)) =
              (4301076939223061 / 11595397094725715 : ℝ)
            by
        norm_num];
        exact hau1050)
  have hat1 :
    (Real.pi / 2 - (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4301076939223061 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4301076939223061 : ℝ) =
              (4301076939223061 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1049)
  have hz1 :
    (5000000000000000 / 4301076939223061 : ℝ) ≤
      1 / Real.sqrt (23679056431509 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4301076939223061 : ℝ) = 1 / (4301076939223061 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8602153878446119 : ℝ) ≤
      (21741886334314884711 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23679056431509 / 32000000000000 : ℝ) ≤
      (750000000000000 / 8602153878446119 : ℝ) := by
    rw [show
        (750000000000000 / 8602153878446119 : ℝ) =
          (3 / 40) / (8602153878446119 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ))) -
        6 * (21741886334314884711 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23679056431509 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23679056431509 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8602153878446119 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ))) -
          6 * (21741886334314884711 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (23679056431509 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23679056431509 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23679056431509 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_640 :
    ((1108830762390958605563 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2922954830394664874721 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8607687906398339 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ))) -
              6 * (434559568317348828441 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (11854766575033 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11854766575033 / 16000000000000 : ℝ)) =
      Real.log (27854766575033 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11854766575033 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11944766575033 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1108830762390958605563 / 2000000000000000000000 : ℝ) ≤
      Real.log (27854766575033 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11944766575033 / 16000000000000 : ℝ) ≤
      (-(2922954830394664874721 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11944766575033 / 16000000000000 : ℝ) = (11944766575033 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11944766575033 / 8000000000000 : ℝ) ≤
            (4008516972605335125279 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8607687906398339 / 10000000000000000 : ℝ) ≤
      Real.sqrt (11854766575033 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11854766575033 / 16000000000000 : ℝ) ≤ (4303843953199171 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11854766575033 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1052 :
    Real.arctan (8607687906398342 / 23194403779404215 : ℝ) ≤
      (3553563874266416429189 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1051 :
    Real.arctan (4303843953199171 / 5000000000000000 : ℝ) ≤
      (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2638880755880843 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4303843953199171 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4303843953199171 / 5000000000000000 : ℝ) /
                (1 + (2638880755880843 / 2000000000000000 : ℝ)) =
              (8607687906398342 / 23194403779404215 : ℝ)
            by
        norm_num];
        exact hau1052)
  have hat1 :
    (Real.pi / 2 - (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4303843953199171 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4303843953199171 : ℝ) =
              (4303843953199171 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1051)
  have hz1 :
    (5000000000000000 / 4303843953199171 : ℝ) ≤
      1 / Real.sqrt (11854766575033 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4303843953199171 : ℝ) = 1 / (4303843953199171 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8607687906398339 : ℝ) ≤
      (434559568317348828441 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11854766575033 / 16000000000000 : ℝ) ≤
      (750000000000000 / 8607687906398339 : ℝ) := by
    rw [show
        (750000000000000 / 8607687906398339 : ℝ) =
          (3 / 40) / (8607687906398339 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ))) -
        6 * (434559568317348828441 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11854766575033 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11854766575033 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8607687906398339 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ))) -
          6 * (434559568317348828441 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (11854766575033 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11854766575033 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11854766575033 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_641 :
    ((2774811481507379783337 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2910205608895841854953 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4306609189357877 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ))) -
              6 * (868563886137522201071 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23740009868623 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23740009868623 / 32000000000000 : ℝ)) =
      Real.log (55740009868623 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23740009868623 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23920009868623 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2774811481507379783337 / 5000000000000000000000 : ℝ) ≤
      Real.log (55740009868623 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23920009868623 / 32000000000000 : ℝ) ≤
      (-(2910205608895841854953 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23920009868623 / 32000000000000 : ℝ) = (23920009868623 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23920009868623 / 16000000000000 : ℝ) ≤
            (4021266194104158145047 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4306609189357877 / 5000000000000000 : ℝ) ≤ Real.sqrt (23740009868623 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23740009868623 / 32000000000000 : ℝ) ≤
      (8613218378715757 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23740009868623 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1054 :
    Real.arctan (8613218378715757 / 23198012382152354 : ℝ) ≤
      (1777575906847914134599 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1053 :
    Real.arctan (8613218378715757 / 10000000000000000 : ℝ) ≤
      (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6599006191076177 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8613218378715757 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8613218378715757 / 10000000000000000 : ℝ) /
                (1 + (6599006191076177 / 5000000000000000 : ℝ)) =
              (8613218378715757 / 23198012382152354 : ℝ)
            by
        norm_num];
        exact hau1054)
  have hat1 :
    (Real.pi / 2 - (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8613218378715757 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8613218378715757 : ℝ) =
              (8613218378715757 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1053)
  have hz1 :
    (10000000000000000 / 8613218378715757 : ℝ) ≤
      1 / Real.sqrt (23740009868623 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8613218378715757 : ℝ) =
          1 / (8613218378715757 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4306609189357877 : ℝ) ≤
      (868563886137522201071 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23740009868623 / 32000000000000 : ℝ) ≤
      (375000000000000 / 4306609189357877 : ℝ) := by
    rw [show
        (375000000000000 / 4306609189357877 : ℝ) =
          (3 / 40) / (4306609189357877 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ))) -
        6 * (868563886137522201071 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23740009868623 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23740009868623 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4306609189357877 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ))) -
          6 * (868563886137522201071 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (23740009868623 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23740009868623 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23740009868623 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_642 :
    ((5555089124548337093933 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2897472620967558860071 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4309372651121549 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (355673786674076914369 / 1000000000000000000000 : ℝ))) -
              6 * (217002424619864156391 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1188524329359 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1188524329359 / 1600000000000 : ℝ)) =
      Real.log (2788524329359 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1188524329359 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1197524329359 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5555089124548337093933 / 10000000000000000000000 : ℝ) ≤
      Real.log (2788524329359 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1197524329359 / 1600000000000 : ℝ) ≤
      (-(2897472620967558860071 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (1197524329359 / 1600000000000 : ℝ) = (1197524329359 / 800000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1197524329359 / 800000000000 : ℝ) ≤
            (4033999182032441139929 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4309372651121549 / 5000000000000000 : ℝ) ≤ Real.sqrt (1188524329359 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1188524329359 / 1600000000000 : ℝ) ≤ (8618745302243101 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1188524329359 / 1600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1056 :
    Real.arctan (8618745302243101 / 23201619998505391 : ℝ) ≤
      (355673786674076914369 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1055 :
    Real.arctan (8618745302243101 / 10000000000000000 : ℝ) ≤
      (2 * (355673786674076914369 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13201619998505391 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8618745302243101 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8618745302243101 / 10000000000000000 : ℝ) /
                (1 + (13201619998505391 / 10000000000000000 : ℝ)) =
              (8618745302243101 / 23201619998505391 : ℝ)
            by
        norm_num];
        exact hau1056)
  have hat1 :
    (Real.pi / 2 - (2 * (355673786674076914369 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8618745302243101 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8618745302243101 : ℝ) =
              (8618745302243101 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1055)
  have hz1 :
    (10000000000000000 / 8618745302243101 : ℝ) ≤
      1 / Real.sqrt (1188524329359 / 1600000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8618745302243101 : ℝ) =
          1 / (8618745302243101 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4309372651121549 : ℝ) ≤
      (217002424619864156391 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1188524329359 / 1600000000000 : ℝ) ≤
      (375000000000000 / 4309372651121549 : ℝ) := by
    rw [show
        (375000000000000 / 4309372651121549 : ℝ) =
          (3 / 40) / (4309372651121549 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (355673786674076914369 / 1000000000000000000000 : ℝ))) -
        6 * (217002424619864156391 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1188524329359 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1188524329359 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4309372651121549 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (355673786674076914369 / 1000000000000000000000 : ℝ))) -
          6 * (217002424619864156391 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1188524329359 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1188524329359 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1188524329359 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_643 :
    ((222422091992879484073 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2884755825322004909539 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2156067170950793 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ))) -
              6 * (216864142568515565517 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (23800963305737 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23800963305737 / 32000000000000 : ℝ)) =
      Real.log (55800963305737 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23800963305737 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23980963305737 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (222422091992879484073 / 400000000000000000000 : ℝ) ≤
      Real.log (55800963305737 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23980963305737 / 32000000000000 : ℝ) ≤
      (-(2884755825322004909539 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23980963305737 / 32000000000000 : ℝ) = (23980963305737 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23980963305737 / 16000000000000 : ℝ) ≤
            (4046715977677995090461 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2156067170950793 / 2500000000000000 : ℝ) ≤ Real.sqrt (23800963305737 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23800963305737 / 32000000000000 : ℝ) ≤ (344970747352127 / 400000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23800963305737 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1058 :
    Real.arctan (8624268683803175 / 23205226629271764 : ℝ) ≤
      (3558322037419228638997 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1057 :
    Real.arctan (344970747352127 / 400000000000000 : ℝ) ≤
      (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3301306657317941 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (344970747352127 / 400000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (344970747352127 / 400000000000000 : ℝ) /
                (1 + (3301306657317941 / 2500000000000000 : ℝ)) =
              (8624268683803175 / 23205226629271764 : ℝ)
            by
        norm_num];
        exact hau1058)
  have hat1 :
    (Real.pi / 2 - (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (400000000000000 / 344970747352127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 344970747352127 : ℝ) =
              (344970747352127 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau1057)
  have hz1 :
    (400000000000000 / 344970747352127 : ℝ) ≤
      1 / Real.sqrt (23800963305737 / 32000000000000 : ℝ) := by
    rw [show (400000000000000 / 344970747352127 : ℝ) = 1 / (344970747352127 / 400000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2156067170950793 : ℝ) ≤
      (216864142568515565517 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23800963305737 / 32000000000000 : ℝ) ≤
      (187500000000000 / 2156067170950793 : ℝ) := by
    rw [show
        (187500000000000 / 2156067170950793 : ℝ) =
          (3 / 40) / (2156067170950793 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ))) -
        6 * (216864142568515565517 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23800963305737 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23800963305737 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2156067170950793 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ))) -
          6 * (216864142568515565517 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (23800963305737 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23800963305737 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23800963305737 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_644 :
    ((69575156151210255373 / 125000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(718013795207170907293 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((539361783137309 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (889976082434089063109 / 2500000000000000000000 : ℝ))) -
              6 * (866904498149987081409 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11915720012147 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11915720012147 / 16000000000000 : ℝ)) =
      Real.log (27915720012147 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11915720012147 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (12005720012147 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (69575156151210255373 / 125000000000000000000 : ℝ) ≤
      Real.log (27915720012147 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (12005720012147 / 16000000000000 : ℝ) ≤
      (-(718013795207170907293 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (12005720012147 / 16000000000000 : ℝ) = (12005720012147 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12005720012147 / 8000000000000 : ℝ) ≤
            (1014854155542829092707 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (539361783137309 / 625000000000000 : ℝ) ≤ Real.sqrt (11915720012147 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11915720012147 / 16000000000000 : ℝ) ≤
      (8629788530196947 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11915720012147 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1060 :
    Real.arctan (8629788530196947 / 23208832275258807 : ℝ) ≤
      (889976082434089063109 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1059 :
    Real.arctan (8629788530196947 / 10000000000000000 : ℝ) ≤
      (2 * (889976082434089063109 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13208832275258807 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8629788530196947 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8629788530196947 / 10000000000000000 : ℝ) /
                (1 + (13208832275258807 / 10000000000000000 : ℝ)) =
              (8629788530196947 / 23208832275258807 : ℝ)
            by
        norm_num];
        exact hau1060)
  have hat1 :
    (Real.pi / 2 - (2 * (889976082434089063109 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8629788530196947 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8629788530196947 : ℝ) =
              (8629788530196947 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1059)
  have hz1 :
    (10000000000000000 / 8629788530196947 : ℝ) ≤
      1 / Real.sqrt (11915720012147 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8629788530196947 : ℝ) =
          1 / (8629788530196947 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 539361783137309 : ℝ) ≤
      (866904498149987081409 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11915720012147 / 16000000000000 : ℝ) ≤
      (46875000000000 / 539361783137309 : ℝ) := by
    rw [show
        (46875000000000 / 539361783137309 : ℝ) =
          (3 / 40) / (539361783137309 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (889976082434089063109 / 2500000000000000000000 : ℝ))) -
        6 * (866904498149987081409 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11915720012147 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11915720012147 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((539361783137309 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (889976082434089063109 / 2500000000000000000000 : ℝ))) -
          6 * (866904498149987081409 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (11915720012147 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11915720012147 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11915720012147 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_645 :
    ((5576923940667797187807 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2846702181558542557229 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8640817644580863 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ))) -
              6 * (865803508735303275437 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (746637295669 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (746637295669 / 1000000000000 : ℝ)) =
      Real.log (1746637295669 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((746637295669 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (752262295669 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5576923940667797187807 / 10000000000000000000000 : ℝ) ≤
      Real.log (1746637295669 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (752262295669 / 1000000000000 : ℝ) ≤
      (-(2846702181558542557229 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (752262295669 / 1000000000000 : ℝ) = (752262295669 / 500000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (752262295669 / 500000000000 : ℝ) ≤
            (4084769621441457442771 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8640817644580863 / 10000000000000000 : ℝ) ≤ Real.sqrt (746637295669 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (746637295669 / 1000000000000 : ℝ) ≤ (4320408822290433 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (746637295669 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau1062 :
    Real.arctan (4320408822290433 / 11608020308059366 : ℝ) ≤
      (3563063295243344731693 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1061 :
    Real.arctan (4320408822290433 / 5000000000000000 : ℝ) ≤
      (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3304010154029683 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (4320408822290433 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4320408822290433 / 5000000000000000 : ℝ) /
                (1 + (3304010154029683 / 2500000000000000 : ℝ)) =
              (4320408822290433 / 11608020308059366 : ℝ)
            by
        norm_num];
        exact hau1062)
  have hat1 :
    (Real.pi / 2 - (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4320408822290433 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4320408822290433 : ℝ) =
              (4320408822290433 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1061)
  have hz1 :
    (5000000000000000 / 4320408822290433 : ℝ) ≤
      1 / Real.sqrt (746637295669 / 1000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4320408822290433 : ℝ) = 1 / (4320408822290433 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2880272548193621 : ℝ) ≤
      (865803508735303275437 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (746637295669 / 1000000000000 : ℝ) ≤
      (250000000000000 / 2880272548193621 : ℝ) := by
    rw [show
        (250000000000000 / 2880272548193621 : ℝ) =
          (3 / 40) / (8640817644580863 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ))) -
        6 * (865803508735303275437 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (746637295669 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (746637295669 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8640817644580863 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ))) -
          6 * (865803508735303275437 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (746637295669 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (746637295669 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (746637295669 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_646 :
    ((1395982290881571788087 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(283044465619030769971 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8647897332212889 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (356508924778024978169 / 1000000000000000000000 : ℝ))) -
              6 * (865098242589412292353 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (765809953469387 / 1024000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (765809953469387 / 1024000000000000 : ℝ)) =
      Real.log (1789809953469387 / 1024000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((765809953469387 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (771569953469387 / 1024000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1395982290881571788087 / 2500000000000000000000 : ℝ) ≤
      Real.log (1789809953469387 / 1024000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (771569953469387 / 1024000000000000 : ℝ) ≤
      (-(283044465619030769971 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (771569953469387 / 1024000000000000 : ℝ) =
            (771569953469387 / 512000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (771569953469387 / 512000000000000 : ℝ) ≤
            (410102714680969230029 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8647897332212889 / 10000000000000000 : ℝ) ≤
      Real.sqrt (765809953469387 / 1024000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (765809953469387 / 1024000000000000 : ℝ) ≤
      (2161974333053223 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (765809953469387 / 1024000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1064 :
    Real.arctan (665222871708684 / 1786205422491955 : ℝ) ≤
      (356508924778024978169 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1063 :
    Real.arctan (2161974333053223 / 2500000000000000 : ℝ) ≤
      (2 * (356508924778024978169 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2644134098479083 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2161974333053223 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2161974333053223 / 2500000000000000 : ℝ) /
                (1 + (2644134098479083 / 2000000000000000 : ℝ)) =
              (665222871708684 / 1786205422491955 : ℝ)
            by
        norm_num];
        exact hau1064)
  have hat1 :
    (Real.pi / 2 - (2 * (356508924778024978169 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2161974333053223 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2161974333053223 : ℝ) =
              (2161974333053223 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1063)
  have hz1 :
    (2500000000000000 / 2161974333053223 : ℝ) ≤
      1 / Real.sqrt (765809953469387 / 1024000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2161974333053223 : ℝ) = 1 / (2161974333053223 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2882632444070963 : ℝ) ≤
      (865098242589412292353 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (765809953469387 / 1024000000000000 : ℝ) ≤
      (250000000000000 / 2882632444070963 : ℝ) := by
    rw [show
        (250000000000000 / 2882632444070963 : ℝ) =
          (3 / 40) / (8647897332212889 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (356508924778024978169 / 1000000000000000000000 : ℝ))) -
        6 * (865098242589412292353 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (765809953469387 / 1024000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (765809953469387 / 1024000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8647897332212889 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (356508924778024978169 / 1000000000000000000000 : ℝ))) -
          6 * (865098242589412292353 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (765809953469387 / 1024000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (765809953469387 / 1024000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (765809953469387 / 1024000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_647 :
    ((2795464741252561992059 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1407106759320460963231 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4327485614363427 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (356711212603540415007 / 1000000000000000000000 : ℝ))) -
              6 * (432197348567961835751 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (383531658086859 / 512000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (383531658086859 / 512000000000000 : ℝ)) =
      Real.log (895531658086859 / 512000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((383531658086859 / 512000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (386411658086859 / 512000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2795464741252561992059 / 5000000000000000000000 : ℝ) ≤
      Real.log (895531658086859 / 512000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (386411658086859 / 512000000000000 : ℝ) ≤
      (-(1407106759320460963231 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (386411658086859 / 512000000000000 : ℝ) =
            (386411658086859 / 256000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (386411658086859 / 256000000000000 : ℝ) ≤
            (2058629142179539036769 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4327485614363427 / 5000000000000000 : ℝ) ≤
      Real.sqrt (383531658086859 / 512000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (383531658086859 / 512000000000000 : ℝ) ≤
      (8654971228726857 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (383531658086859 / 512000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1066 :
    Real.arctan (8654971228726857 / 23225298747857821 : ℝ) ≤
      (356711212603540415007 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1065 :
    Real.arctan (8654971228726857 / 10000000000000000 : ℝ) ≤
      (2 * (356711212603540415007 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13225298747857821 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8654971228726857 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8654971228726857 / 10000000000000000 : ℝ) /
                (1 + (13225298747857821 / 10000000000000000 : ℝ)) =
              (8654971228726857 / 23225298747857821 : ℝ)
            by
        norm_num];
        exact hau1066)
  have hat1 :
    (Real.pi / 2 - (2 * (356711212603540415007 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8654971228726857 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8654971228726857 : ℝ) =
              (8654971228726857 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1065)
  have hz1 :
    (10000000000000000 / 8654971228726857 : ℝ) ≤
      1 / Real.sqrt (383531658086859 / 512000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8654971228726857 : ℝ) =
          1 / (8654971228726857 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1442495204787809 : ℝ) ≤
      (432197348567961835751 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (383531658086859 / 512000000000000 : ℝ) ≤
      (125000000000000 / 1442495204787809 : ℝ) := by
    rw [show
        (125000000000000 / 1442495204787809 : ℝ) =
          (3 / 40) / (4327485614363427 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (356711212603540415007 / 1000000000000000000000 : ℝ))) -
        6 * (432197348567961835751 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (383531658086859 / 512000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (383531658086859 / 512000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4327485614363427 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (356711212603540415007 / 1000000000000000000000 : ℝ))) -
          6 * (432197348567961835751 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (383531658086859 / 512000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (383531658086859 / 512000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (383531658086859 / 512000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_648 :
    ((5597924904465249726207 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1399004341694148145729 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1082754918538849 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ))) -
              6 * (431846432694659931273 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (768316678878049 / 1024000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (768316678878049 / 1024000000000000 : ℝ)) =
      Real.log (1792316678878049 / 1024000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((768316678878049 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (774076678878049 / 1024000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5597924904465249726207 / 10000000000000000000000 : ℝ) ≤
      Real.log (1792316678878049 / 1024000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (774076678878049 / 1024000000000000 : ℝ) ≤
      (-(1399004341694148145729 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (774076678878049 / 1024000000000000 : ℝ) =
            (774076678878049 / 512000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (774076678878049 / 512000000000000 : ℝ) ≤
            (2066731559805851854271 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1082754918538849 / 1250000000000000 : ℝ) ≤
      Real.sqrt (768316678878049 / 1024000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (768316678878049 / 1024000000000000 : ℝ) ≤
      (1732407869662159 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (768316678878049 / 1024000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1068 :
    Real.arctan (1732407869662159 / 4645985076841398 : ℝ) ≤
      (1784565969182207295463 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1067 :
    Real.arctan (1732407869662159 / 2000000000000000 : ℝ) ≤
      (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1322992538420699 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1732407869662159 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1732407869662159 / 2000000000000000 : ℝ) /
                (1 + (1322992538420699 / 1000000000000000 : ℝ)) =
              (1732407869662159 / 4645985076841398 : ℝ)
            by
        norm_num];
        exact hau1068)
  have hat1 :
    (Real.pi / 2 - (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1732407869662159 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1732407869662159 : ℝ) =
              (1732407869662159 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1067)
  have hz1 :
    (2000000000000000 / 1732407869662159 : ℝ) ≤
      1 / Real.sqrt (768316678878049 / 1024000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1732407869662159 : ℝ) = 1 / (1732407869662159 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 1082754918538849 : ℝ) ≤
      (431846432694659931273 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (768316678878049 / 1024000000000000 : ℝ) ≤
      (93750000000000 / 1082754918538849 : ℝ) := by
    rw [show
        (93750000000000 / 1082754918538849 : ℝ) =
          (3 / 40) / (1082754918538849 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ))) -
        6 * (431846432694659931273 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (768316678878049 / 1024000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (768316678878049 / 1024000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1082754918538849 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ))) -
          6 * (431846432694659931273 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (768316678878049 / 1024000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (768316678878049 / 1024000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (768316678878049 / 1024000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
