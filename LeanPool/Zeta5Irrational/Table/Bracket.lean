/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Potential
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # Bracket: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_br :
    ((236122014583635193 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5576823552816418281887 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((769448367338577 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
              6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ))))) ≤
      Real.log (1 + qm) - 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
        2 * Real.sqrt qp * Pfun (Real.sqrt qm) := by
  have hPneg := Pfun_sqrt_qm_neg
  unfold Pfun at hPneg ⊢
  have e1 : Real.log (1 + qm) = Real.log (10059205077 / 10000000000 : ℝ) := by norm_num [qm]
  have e2 : Real.log (qp + (3 / 40) ^ 2) = Real.log (115455079 / 10000000000 : ℝ) := by
    norm_num [qp]
  have hL1 :
    (236122014583635193 / 40000000000000000000 : ℝ) ≤ Real.log (10059205077 / 10000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (115455079 / 10000000000 : ℝ) ≤
      (-(5576823552816418281887 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (115455079 / 10000000000 : ℝ) = (115455079 / 78125000 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115455079 / 78125000 : ℝ) ≤
            (488214274808581718113 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo : (769448354342251 / 10000000000000000 : ℝ) ≤ Real.sqrt qm :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num [qm])
  have hs_hi : Real.sqrt qm ≤ (384724177171127 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num [qm])
  have hp_hi : Real.sqrt qp ≤ (769448367338577 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num [qp])
  have hspos : 0 < Real.sqrt qm := sqrt_qm_pos
  have hau1 :
    Real.arctan (384724177171127 / 5000000000000000 : ℝ) ≤
      (38396760876845215791 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 384724177171127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 384724177171127 : ℝ) =
              (384724177171127 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1)
  have hz1 : (5000000000000000 / 384724177171127 : ℝ) ≤ 1 / Real.sqrt qm := by
    rw [show
        (5000000000000000 / 384724177171127 : ℝ) = 1 / (384724177171127 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau2 :
    Real.arctan (625000000000000000000000000000 / 1536623830262694597801594657771 : ℝ) ≤
      (772599247056886688553 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 769448354342251 : ℝ) ≤
      (2 * (772599247056886688553 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3491138280786563 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 769448354342251 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 769448354342251 : ℝ) /
                (1 + (3491138280786563 / 2500000000000000 : ℝ)) =
              (625000000000000000000000000000 / 1536623830262694597801594657771 : ℝ)
            by
        norm_num];
        exact hau2)
  have hz2 : (3 / 40) / Real.sqrt qm ≤ (750000000000000 / 769448354342251 : ℝ) := by
    rw [show
        (750000000000000 / 769448354342251 : ℝ) =
          (3 / 40) / (769448354342251 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
        6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt qm) - 6 * Real.arctan (3 / 40 / Real.sqrt qm)) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((769448367338577 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
          6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ)))) ≤
      Real.sqrt qp *
        (Real.pi + Real.arctan (1 / Real.sqrt qm) - 6 * Real.arctan (3 / 40 / Real.sqrt qm)) := by
    have h1 := mul_le_mul_of_nonpos_right hp_hi hPneg.le
    have h2 :=
      mul_le_mul_of_nonneg_left hP
        (by norm_num : (0 : ℝ) ≤ (769448367338577 / 10000000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
