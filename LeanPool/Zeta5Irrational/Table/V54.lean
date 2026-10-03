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

/-! # V54: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_649 :
    ((5604915436253217929901 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(695457516331357721269 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4334550852547449 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3571148693088848187633 / 10000000000000000000000 : ℝ))) -
              6 * (862992740403722005993 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (38478502079119 / 51200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38478502079119 / 51200000000000 : ℝ)) =
      Real.log (89678502079119 / 51200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38478502079119 / 51200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (38766502079119 / 51200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5604915436253217929901 / 10000000000000000000000 : ℝ) ≤
      Real.log (89678502079119 / 51200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (38766502079119 / 51200000000000 : ℝ) ≤
      (-(695457516331357721269 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (38766502079119 / 51200000000000 : ℝ) = (38766502079119 / 25600000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38766502079119 / 25600000000000 : ℝ) ≤
            (1037410434418642278731 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4334550852547449 / 5000000000000000 : ℝ) ≤ Real.sqrt (38478502079119 / 51200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38478502079119 / 51200000000000 : ℝ) ≤
      (8669101705094901 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38478502079119 / 51200000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1070 :
    Real.arctan (8669101705094901 / 23234550403140988 : ℝ) ≤
      (3571148693088848187633 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1069 :
    Real.arctan (8669101705094901 / 10000000000000000 : ℝ) ≤
      (2 * (3571148693088848187633 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3308637600785247 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8669101705094901 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8669101705094901 / 10000000000000000 : ℝ) /
                (1 + (3308637600785247 / 2500000000000000 : ℝ)) =
              (8669101705094901 / 23234550403140988 : ℝ)
            by
        norm_num];
        exact hau1070)
  have hat1 :
    (Real.pi / 2 - (2 * (3571148693088848187633 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8669101705094901 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8669101705094901 : ℝ) =
              (8669101705094901 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1069)
  have hz1 :
    (10000000000000000 / 8669101705094901 : ℝ) ≤
      1 / Real.sqrt (38478502079119 / 51200000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8669101705094901 : ℝ) =
          1 / (8669101705094901 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1444850284182483 : ℝ) ≤
      (862992740403722005993 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38478502079119 / 51200000000000 : ℝ) ≤
      (125000000000000 / 1444850284182483 : ℝ) := by
    rw [show
        (125000000000000 / 1444850284182483 : ℝ) =
          (3 / 40) / (4334550852547449 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3571148693088848187633 / 10000000000000000000000 : ℝ))) -
        6 * (862992740403722005993 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38478502079119 / 51200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38478502079119 / 51200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4334550852547449 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3571148693088848187633 / 10000000000000000000000 : ℝ))) -
          6 * (862992740403722005993 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (38478502079119 / 51200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38478502079119 / 51200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38478502079119 / 51200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_650 :
    ((5611901084701233859877 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2765677579757732943883 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4338079156575929 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3573162398496421435577 / 10000000000000000000000 : ℝ))) -
              6 * (215573578818150291501 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (770823404286711 / 1024000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (770823404286711 / 1024000000000000 : ℝ)) =
      Real.log (1794823404286711 / 1024000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((770823404286711 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (776583404286711 / 1024000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5611901084701233859877 / 10000000000000000000000 : ℝ) ≤
      Real.log (1794823404286711 / 1024000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (776583404286711 / 1024000000000000 : ℝ) ≤
      (-(2765677579757732943883 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (776583404286711 / 1024000000000000 : ℝ) =
            (776583404286711 / 512000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (776583404286711 / 512000000000000 : ℝ) ≤
            (4165794223242267056117 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4338079156575929 / 5000000000000000 : ℝ) ≤
      Real.sqrt (770823404286711 / 1024000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (770823404286711 / 1024000000000000 : ℝ) ≤
      (8676158313151861 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (770823404286711 / 1024000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1072 :
    Real.arctan (8676158313151861 / 23239173806354916 : ℝ) ≤
      (3573162398496421435577 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1071 :
    Real.arctan (8676158313151861 / 10000000000000000 : ℝ) ≤
      (2 * (3573162398496421435577 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3309793451588729 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8676158313151861 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8676158313151861 / 10000000000000000 : ℝ) /
                (1 + (3309793451588729 / 2500000000000000 : ℝ)) =
              (8676158313151861 / 23239173806354916 : ℝ)
            by
        norm_num];
        exact hau1072)
  have hat1 :
    (Real.pi / 2 - (2 * (3573162398496421435577 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8676158313151861 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8676158313151861 : ℝ) =
              (8676158313151861 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1071)
  have hz1 :
    (10000000000000000 / 8676158313151861 : ℝ) ≤
      1 / Real.sqrt (770823404286711 / 1024000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8676158313151861 : ℝ) =
          1 / (8676158313151861 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4338079156575929 : ℝ) ≤
      (215573578818150291501 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (770823404286711 / 1024000000000000 : ℝ) ≤
      (375000000000000 / 4338079156575929 : ℝ) := by
    rw [show
        (375000000000000 / 4338079156575929 : ℝ) =
          (3 / 40) / (4338079156575929 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3573162398496421435577 / 10000000000000000000000 : ℝ))) -
        6 * (215573578818150291501 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (770823404286711 / 1024000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (770823404286711 / 1024000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4338079156575929 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3573162398496421435577 / 10000000000000000000000 : ℝ))) -
          6 * (215573578818150291501 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (770823404286711 / 1024000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (770823404286711 / 1024000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (770823404286711 / 1024000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_651 :
    ((112377637132543891181 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2749551142400356585123 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4341604593248587 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (178758653142059377991 / 500000000000000000000 : ℝ))) -
              6 * (861597583128492385527 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (386038383495521 / 512000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (386038383495521 / 512000000000000 : ℝ)) =
      Real.log (898038383495521 / 512000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((386038383495521 / 512000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (388918383495521 / 512000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (112377637132543891181 / 200000000000000000000 : ℝ) ≤
      Real.log (898038383495521 / 512000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (388918383495521 / 512000000000000 : ℝ) ≤
      (-(2749551142400356585123 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (388918383495521 / 512000000000000 : ℝ) =
            (388918383495521 / 256000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (388918383495521 / 256000000000000 : ℝ) ≤
            (4181920660599643414877 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4341604593248587 / 5000000000000000 : ℝ) ≤
      Real.sqrt (386038383495521 / 512000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (386038383495521 / 512000000000000 : ℝ) ≤
      (8683209186497177 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (386038383495521 / 512000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1074 :
    Real.arctan (8683209186497177 / 23243795595540915 : ℝ) ≤
      (178758653142059377991 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1073 :
    Real.arctan (8683209186497177 / 10000000000000000 : ℝ) ≤
      (2 * (178758653142059377991 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2648759119108183 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8683209186497177 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8683209186497177 / 10000000000000000 : ℝ) /
                (1 + (2648759119108183 / 2000000000000000 : ℝ)) =
              (8683209186497177 / 23243795595540915 : ℝ)
            by
        norm_num];
        exact hau1074)
  have hat1 :
    (Real.pi / 2 - (2 * (178758653142059377991 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8683209186497177 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8683209186497177 : ℝ) =
              (8683209186497177 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1073)
  have hz1 :
    (10000000000000000 / 8683209186497177 : ℝ) ≤
      1 / Real.sqrt (386038383495521 / 512000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8683209186497177 : ℝ) =
          1 / (8683209186497177 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4341604593248587 : ℝ) ≤
      (861597583128492385527 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (386038383495521 / 512000000000000 : ℝ) ≤
      (375000000000000 / 4341604593248587 : ℝ) := by
    rw [show
        (375000000000000 / 4341604593248587 : ℝ) =
          (3 / 40) / (4341604593248587 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (178758653142059377991 / 500000000000000000000 : ℝ))) -
        6 * (861597583128492385527 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (386038383495521 / 512000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (386038383495521 / 512000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4341604593248587 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (178758653142059377991 / 500000000000000000000 : ℝ))) -
          6 * (861597583128492385527 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (386038383495521 / 512000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (386038383495521 / 512000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (386038383495521 / 512000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_652 :
    ((2812928879417364386841 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(136672533468778197849 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2172563584772373 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (894295173585930991351 / 2500000000000000000000 : ℝ))) -
              6 * (215225634285677686871 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (773330129695373 / 1024000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (773330129695373 / 1024000000000000 : ℝ)) =
      Real.log (1797330129695373 / 1024000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((773330129695373 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (779090129695373 / 1024000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2812928879417364386841 / 5000000000000000000000 : ℝ) ≤
      Real.log (1797330129695373 / 1024000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (779090129695373 / 1024000000000000 : ℝ) ≤
      (-(136672533468778197849 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (779090129695373 / 1024000000000000 : ℝ) =
            (779090129695373 / 512000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (779090129695373 / 512000000000000 : ℝ) ≤
            (209901056681221802151 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2172563584772373 / 2500000000000000 : ℝ) ≤
      Real.sqrt (773330129695373 / 1024000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (773330129695373 / 1024000000000000 : ℝ) ≤
      (1738050867817899 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (773330129695373 / 1024000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1076 :
    Real.arctan (1738050867817899 / 4649683154477635 : ℝ) ≤
      (894295173585930991351 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1075 :
    Real.arctan (1738050867817899 / 2000000000000000 : ℝ) ≤
      (2 * (894295173585930991351 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (529936630895527 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (1738050867817899 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1738050867817899 / 2000000000000000 : ℝ) /
                (1 + (529936630895527 / 400000000000000 : ℝ)) =
              (1738050867817899 / 4649683154477635 : ℝ)
            by
        norm_num];
        exact hau1076)
  have hat1 :
    (Real.pi / 2 - (2 * (894295173585930991351 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1738050867817899 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1738050867817899 : ℝ) =
              (1738050867817899 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1075)
  have hz1 :
    (2000000000000000 / 1738050867817899 : ℝ) ≤
      1 / Real.sqrt (773330129695373 / 1024000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1738050867817899 : ℝ) = 1 / (1738050867817899 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 724187861590791 : ℝ) ≤
      (215225634285677686871 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (773330129695373 / 1024000000000000 : ℝ) ≤
      (62500000000000 / 724187861590791 : ℝ) := by
    rw [show
        (62500000000000 / 724187861590791 : ℝ) =
          (3 / 40) / (2172563584772373 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (894295173585930991351 / 2500000000000000000000 : ℝ))) -
        6 * (215225634285677686871 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (773330129695373 / 1024000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (773330129695373 / 1024000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2172563584772373 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (894295173585930991351 / 2500000000000000000000 : ℝ))) -
          6 * (215225634285677686871 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (773330129695373 / 1024000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (773330129695373 / 1024000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (773330129695373 / 1024000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_653 :
    ((5632828798113236739333 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(543475215442021519619 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8697293784830921 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3579185301191316278443 / 10000000000000000000000 : ℝ))) -
              6 * (21505229263126765113 / 250000000000000000000 : ℝ)))) ≤
      Vfield (96822936549963 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (96822936549963 / 128000000000000 : ℝ)) =
      Real.log (224822936549963 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((96822936549963 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (97542936549963 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5632828798113236739333 / 10000000000000000000000 : ℝ) ≤
      Real.log (224822936549963 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (97542936549963 / 128000000000000 : ℝ) ≤
      (-(543475215442021519619 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (97542936549963 / 128000000000000 : ℝ) = (97542936549963 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (97542936549963 / 64000000000000 : ℝ) ≤
            (842819145157978480381 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8697293784830921 / 10000000000000000 : ℝ) ≤
      Real.sqrt (96822936549963 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (96822936549963 / 128000000000000 : ℝ) ≤
      (2174323446207731 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (96822936549963 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1078 :
    Real.arctan (8697293784830924 / 23253034338582941 : ℝ) ≤
      (3579185301191316278443 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1077 :
    Real.arctan (2174323446207731 / 2500000000000000 : ℝ) ≤
      (2 * (3579185301191316278443 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13253034338582941 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2174323446207731 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2174323446207731 / 2500000000000000 : ℝ) /
                (1 + (13253034338582941 / 10000000000000000 : ℝ)) =
              (8697293784830924 / 23253034338582941 : ℝ)
            by
        norm_num];
        exact hau1078)
  have hat1 :
    (Real.pi / 2 - (2 * (3579185301191316278443 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2174323446207731 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2174323446207731 : ℝ) =
              (2174323446207731 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1077)
  have hz1 :
    (2500000000000000 / 2174323446207731 : ℝ) ≤
      1 / Real.sqrt (96822936549963 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2174323446207731 : ℝ) = 1 / (2174323446207731 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8697293784830921 : ℝ) ≤
      (21505229263126765113 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (96822936549963 / 128000000000000 : ℝ) ≤
      (750000000000000 / 8697293784830921 : ℝ) := by
    rw [show
        (750000000000000 / 8697293784830921 : ℝ) =
          (3 / 40) / (8697293784830921 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3579185301191316278443 / 10000000000000000000000 : ℝ))) -
        6 * (21505229263126765113 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (96822936549963 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (96822936549963 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8697293784830921 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3579185301191316278443 / 10000000000000000000000 : ℝ))) -
          6 * (21505229263126765113 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (96822936549963 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (96822936549963 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (96822936549963 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_654 :
    ((5639794981237929828231 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1350663641416316901041 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2176081884391839 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1790593445769071451627 / 5000000000000000000000 : ℝ))) -
              6 * (85951747652360666837 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (155167371020807 / 204800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (155167371020807 / 204800000000000 : ℝ)) =
      Real.log (359967371020807 / 204800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((155167371020807 / 204800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (156319371020807 / 204800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5639794981237929828231 / 10000000000000000000000 : ℝ) ≤
      Real.log (359967371020807 / 204800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (156319371020807 / 204800000000000 : ℝ) ≤
      (-(1350663641416316901041 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (156319371020807 / 204800000000000 : ℝ) =
            (156319371020807 / 102400000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (156319371020807 / 102400000000000 : ℝ) ≤
            (2115072260083683098959 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2176081884391839 / 2500000000000000 : ℝ) ≤
      Real.sqrt (155167371020807 / 204800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (155167371020807 / 204800000000000 : ℝ) ≤
      (8704327537567359 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (155167371020807 / 204800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1080 :
    Real.arctan (8704327537567359 / 23257651295808523 : ℝ) ≤
      (1790593445769071451627 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1079 :
    Real.arctan (8704327537567359 / 10000000000000000 : ℝ) ≤
      (2 * (1790593445769071451627 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13257651295808523 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8704327537567359 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8704327537567359 / 10000000000000000 : ℝ) /
                (1 + (13257651295808523 / 10000000000000000 : ℝ)) =
              (8704327537567359 / 23257651295808523 : ℝ)
            by
        norm_num];
        exact hau1080)
  have hat1 :
    (Real.pi / 2 - (2 * (1790593445769071451627 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8704327537567359 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8704327537567359 : ℝ) =
              (8704327537567359 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1079)
  have hz1 :
    (10000000000000000 / 8704327537567359 : ℝ) ≤
      1 / Real.sqrt (155167371020807 / 204800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8704327537567359 : ℝ) =
          1 / (8704327537567359 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 725360628130613 : ℝ) ≤
      (85951747652360666837 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (155167371020807 / 204800000000000 : ℝ) ≤
      (62500000000000 / 725360628130613 : ℝ) := by
    rw [show
        (62500000000000 / 725360628130613 : ℝ) =
          (3 / 40) / (2176081884391839 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1790593445769071451627 / 5000000000000000000000 : ℝ))) -
        6 * (85951747652360666837 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (155167371020807 / 204800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (155167371020807 / 204800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2176081884391839 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1790593445769071451627 / 5000000000000000000000 : ℝ))) -
          6 * (85951747652360666837 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (155167371020807 / 204800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (155167371020807 / 204800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (155167371020807 / 204800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_655 :
    ((1411689078742467514661 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2685304203571106785121 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4355677805544397 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1791592736752728819669 / 5000000000000000000000 : ℝ))) -
              6 * (107353431053037252639 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (388545108904183 / 512000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (388545108904183 / 512000000000000 : ℝ)) =
      Real.log (900545108904183 / 512000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((388545108904183 / 512000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (391425108904183 / 512000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1411689078742467514661 / 2500000000000000000000 : ℝ) ≤
      Real.log (900545108904183 / 512000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (391425108904183 / 512000000000000 : ℝ) ≤
      (-(2685304203571106785121 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (391425108904183 / 512000000000000 : ℝ) =
            (391425108904183 / 256000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (391425108904183 / 256000000000000 : ℝ) ≤
            (4246167599428893214879 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4355677805544397 / 5000000000000000 : ℝ) ≤
      Real.sqrt (388545108904183 / 512000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (388545108904183 / 512000000000000 : ℝ) ≤
      (8711355611088797 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (388545108904183 / 512000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1082 :
    Real.arctan (8711355611088797 / 23262266645745298 : ℝ) ≤
      (1791592736752728819669 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1081 :
    Real.arctan (8711355611088797 / 10000000000000000 : ℝ) ≤
      (2 * (1791592736752728819669 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6631133322872649 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8711355611088797 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8711355611088797 / 10000000000000000 : ℝ) /
                (1 + (6631133322872649 / 5000000000000000 : ℝ)) =
              (8711355611088797 / 23262266645745298 : ℝ)
            by
        norm_num];
        exact hau1082)
  have hat1 :
    (Real.pi / 2 - (2 * (1791592736752728819669 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8711355611088797 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8711355611088797 : ℝ) =
              (8711355611088797 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1081)
  have hz1 :
    (10000000000000000 / 8711355611088797 : ℝ) ≤
      1 / Real.sqrt (388545108904183 / 512000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8711355611088797 : ℝ) =
          1 / (8711355611088797 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4355677805544397 : ℝ) ≤
      (107353431053037252639 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (388545108904183 / 512000000000000 : ℝ) ≤
      (375000000000000 / 4355677805544397 : ℝ) := by
    rw [show
        (375000000000000 / 4355677805544397 : ℝ) =
          (3 / 40) / (4355677805544397 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1791592736752728819669 / 5000000000000000000000 : ℝ))) -
        6 * (107353431053037252639 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (388545108904183 / 512000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (388545108904183 / 512000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4355677805544397 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1791592736752728819669 / 5000000000000000000000 : ℝ))) -
          6 * (107353431053037252639 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (388545108904183 / 512000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (388545108904183 / 512000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (388545108904183 / 512000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_656 :
    ((5660664461229229342117 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1326667430844514298871 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((872539477536907 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1793586822311514017451 / 5000000000000000000000 : ℝ))) -
              6 * (428726181632072282809 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (194899235804257 / 256000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (194899235804257 / 256000000000000 : ℝ)) =
      Real.log (450899235804257 / 256000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((194899235804257 / 256000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (196339235804257 / 256000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5660664461229229342117 / 10000000000000000000000 : ℝ) ≤
      Real.log (450899235804257 / 256000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (196339235804257 / 256000000000000 : ℝ) ≤
      (-(1326667430844514298871 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (196339235804257 / 256000000000000 : ℝ) =
            (196339235804257 / 128000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (196339235804257 / 128000000000000 : ℝ) ≤
            (2139068470655485701129 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (872539477536907 / 1000000000000000 : ℝ) ≤
      Real.sqrt (194899235804257 / 256000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (194899235804257 / 256000000000000 : ℝ) ≤
      (8725394775369073 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (194899235804257 / 256000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1084 :
    Real.arctan (8725394775369073 / 23271492530459333 : ℝ) ≤
      (1793586822311514017451 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1083 :
    Real.arctan (8725394775369073 / 10000000000000000 : ℝ) ≤
      (2 * (1793586822311514017451 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13271492530459333 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8725394775369073 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8725394775369073 / 10000000000000000 : ℝ) /
                (1 + (13271492530459333 / 10000000000000000 : ℝ)) =
              (8725394775369073 / 23271492530459333 : ℝ)
            by
        norm_num];
        exact hau1084)
  have hat1 :
    (Real.pi / 2 - (2 * (1793586822311514017451 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8725394775369073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8725394775369073 : ℝ) =
              (8725394775369073 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1083)
  have hz1 :
    (10000000000000000 / 8725394775369073 : ℝ) ≤
      1 / Real.sqrt (194899235804257 / 256000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8725394775369073 : ℝ) =
          1 / (8725394775369073 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 872539477536907 : ℝ) ≤
      (428726181632072282809 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (194899235804257 / 256000000000000 : ℝ) ≤
      (75000000000000 / 872539477536907 : ℝ) := by
    rw [show
        (75000000000000 / 872539477536907 : ℝ) =
          (3 / 40) / (872539477536907 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1793586822311514017451 / 5000000000000000000000 : ℝ))) -
        6 * (428726181632072282809 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (194899235804257 / 256000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (194899235804257 / 256000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((872539477536907 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1793586822311514017451 / 5000000000000000000000 : ℝ))) -
          6 * (428726181632072282809 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (194899235804257 / 256000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (194899235804257 / 256000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (194899235804257 / 256000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_657 :
    ((2837276645349158187007 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(524293479615471020593 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1092426423360713 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (897787469715603738619 / 2500000000000000000000 : ℝ))) -
              6 * (85608386208098783843 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (78210366862569 / 102400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (78210366862569 / 102400000000000 : ℝ)) =
      Real.log (180610366862569 / 102400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((78210366862569 / 102400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (78786366862569 / 102400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2837276645349158187007 / 5000000000000000000000 : ℝ) ≤
      Real.log (180610366862569 / 102400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (78786366862569 / 102400000000000 : ℝ) ≤
      (-(524293479615471020593 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (78786366862569 / 102400000000000 : ℝ) = (78786366862569 / 51200000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (78786366862569 / 51200000000000 : ℝ) ≤
            (862000880984528979407 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1092426423360713 / 1250000000000000 : ℝ) ≤
      Real.sqrt (78210366862569 / 102400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (78210366862569 / 102400000000000 : ℝ) ≤
      (8739411386885707 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (78210366862569 / 102400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1086 :
    Real.arctan (794491944262337 / 2116428364191795 : ℝ) ≤
      (897787469715603738619 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1085 :
    Real.arctan (8739411386885707 / 10000000000000000 : ℝ) ≤
      (2 * (897787469715603738619 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2656142401221949 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8739411386885707 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8739411386885707 / 10000000000000000 : ℝ) /
                (1 + (2656142401221949 / 2000000000000000 : ℝ)) =
              (794491944262337 / 2116428364191795 : ℝ)
            by
        norm_num];
        exact hau1086)
  have hat1 :
    (Real.pi / 2 - (2 * (897787469715603738619 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8739411386885707 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8739411386885707 : ℝ) =
              (8739411386885707 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1085)
  have hz1 :
    (10000000000000000 / 8739411386885707 : ℝ) ≤
      1 / Real.sqrt (78210366862569 / 102400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8739411386885707 : ℝ) =
          1 / (8739411386885707 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 1092426423360713 : ℝ) ≤
      (85608386208098783843 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (78210366862569 / 102400000000000 : ℝ) ≤
      (93750000000000 / 1092426423360713 : ℝ) := by
    rw [show
        (93750000000000 / 1092426423360713 : ℝ) =
          (3 / 40) / (1092426423360713 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (897787469715603738619 / 2500000000000000000000 : ℝ))) -
        6 * (85608386208098783843 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (78210366862569 / 102400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (78210366862569 / 102400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1092426423360713 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (897787469715603738619 / 2500000000000000000000 : ℝ))) -
          6 * (85608386208098783843 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (78210366862569 / 102400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (78210366862569 / 102400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (78210366862569 / 102400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_658 :
    ((711052857120031112197 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1294850582738612798973 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2188351388494561 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (898778560006669417019 / 2500000000000000000000 : ℝ))) -
              6 * (17094437850020888933 / 200000000000000000000 : ℝ)))) ≤
      Vfield (49038149627147 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (49038149627147 / 64000000000000 : ℝ)) =
      Real.log (113038149627147 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((49038149627147 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (49398149627147 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (711052857120031112197 / 1250000000000000000000 : ℝ) ≤
      Real.log (113038149627147 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (49398149627147 / 64000000000000 : ℝ) ≤
      (-(1294850582738612798973 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (49398149627147 / 64000000000000 : ℝ) = (49398149627147 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49398149627147 / 32000000000000 : ℝ) ≤
            (2170885318761387201027 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2188351388494561 / 2500000000000000 : ℝ) ≤ Real.sqrt (49038149627147 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (49038149627147 / 64000000000000 : ℝ) ≤
      (8753405553978247 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (49038149627147 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1088 :
    Real.arctan (8753405553978247 / 23289925086034804 : ℝ) ≤
      (898778560006669417019 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1087 :
    Real.arctan (8753405553978247 / 10000000000000000 : ℝ) ≤
      (2 * (898778560006669417019 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3322481271508701 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8753405553978247 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8753405553978247 / 10000000000000000 : ℝ) /
                (1 + (3322481271508701 / 2500000000000000 : ℝ)) =
              (8753405553978247 / 23289925086034804 : ℝ)
            by
        norm_num];
        exact hau1088)
  have hat1 :
    (Real.pi / 2 - (2 * (898778560006669417019 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8753405553978247 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8753405553978247 : ℝ) =
              (8753405553978247 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1087)
  have hz1 :
    (10000000000000000 / 8753405553978247 : ℝ) ≤
      1 / Real.sqrt (49038149627147 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8753405553978247 : ℝ) =
          1 / (8753405553978247 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2188351388494561 : ℝ) ≤
      (17094437850020888933 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (49038149627147 / 64000000000000 : ℝ) ≤
      (187500000000000 / 2188351388494561 : ℝ) := by
    rw [show
        (187500000000000 / 2188351388494561 : ℝ) =
          (3 / 40) / (2188351388494561 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (898778560006669417019 / 2500000000000000000000 : ℝ))) -
        6 * (17094437850020888933 / 200000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (49038149627147 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (49038149627147 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2188351388494561 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (898778560006669417019 / 2500000000000000000000 : ℝ))) -
          6 * (17094437850020888933 / 200000000000000000000 : ℝ))) ≤
      Real.sqrt (49038149627147 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (49038149627147 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (49038149627147 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_659 :
    ((1425568303343877683293 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(319754440347319404593 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4383688692060797 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3599066791409163219773 / 10000000000000000000000 : ℝ))) -
              6 * (853366402731951753291 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (393558559721507 / 512000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (393558559721507 / 512000000000000 : ℝ)) =
      Real.log (905558559721507 / 512000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((393558559721507 / 512000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (396438559721507 / 512000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1425568303343877683293 / 2500000000000000000000 : ℝ) ≤
      Real.log (905558559721507 / 512000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (396438559721507 / 512000000000000 : ℝ) ≤
      (-(319754440347319404593 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (396438559721507 / 512000000000000 : ℝ) =
            (396438559721507 / 256000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (396438559721507 / 256000000000000 : ℝ) ≤
            (546679535027680595407 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4383688692060797 / 5000000000000000 : ℝ) ≤
      Real.sqrt (393558559721507 / 512000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (393558559721507 / 512000000000000 : ℝ) ≤
      (8767377384121597 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (393558559721507 / 512000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1090 :
    Real.arctan (8767377384121597 / 23299131783526578 : ℝ) ≤
      (3599066791409163219773 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1089 :
    Real.arctan (8767377384121597 / 10000000000000000 : ℝ) ≤
      (2 * (3599066791409163219773 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6649565891763289 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8767377384121597 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8767377384121597 / 10000000000000000 : ℝ) /
                (1 + (6649565891763289 / 5000000000000000 : ℝ)) =
              (8767377384121597 / 23299131783526578 : ℝ)
            by
        norm_num];
        exact hau1090)
  have hat1 :
    (Real.pi / 2 - (2 * (3599066791409163219773 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8767377384121597 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8767377384121597 : ℝ) =
              (8767377384121597 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1089)
  have hz1 :
    (10000000000000000 / 8767377384121597 : ℝ) ≤
      1 / Real.sqrt (393558559721507 / 512000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8767377384121597 : ℝ) =
          1 / (8767377384121597 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4383688692060797 : ℝ) ≤
      (853366402731951753291 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (393558559721507 / 512000000000000 : ℝ) ≤
      (375000000000000 / 4383688692060797 : ℝ) := by
    rw [show
        (375000000000000 / 4383688692060797 : ℝ) =
          (3 / 40) / (4383688692060797 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3599066791409163219773 / 10000000000000000000000 : ℝ))) -
        6 * (853366402731951753291 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (393558559721507 / 512000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (393558559721507 / 512000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4383688692060797 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3599066791409163219773 / 10000000000000000000000 : ℝ))) -
          6 * (853366402731951753291 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (393558559721507 / 512000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (393558559721507 / 512000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (393558559721507 / 512000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_660 :
    ((5716104413083145056471 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2526469834942398681093 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4390663491967827 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (720601519159810012143 / 2000000000000000000000 : ℝ))) -
              6 * (6656385480894487883 / 78125000000000000000 : ℝ)))) ≤
      Vfield (197405961212919 / 256000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (197405961212919 / 256000000000000 : ℝ)) =
      Real.log (453405961212919 / 256000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((197405961212919 / 256000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (198845961212919 / 256000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5716104413083145056471 / 10000000000000000000000 : ℝ) ≤
      Real.log (453405961212919 / 256000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (198845961212919 / 256000000000000 : ℝ) ≤
      (-(2526469834942398681093 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (198845961212919 / 256000000000000 : ℝ) =
            (198845961212919 / 128000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (198845961212919 / 128000000000000 : ℝ) ≤
            (4405001968057601318907 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4390663491967827 / 5000000000000000 : ℝ) ≤
      Real.sqrt (197405961212919 / 256000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (197405961212919 / 256000000000000 : ℝ) ≤
      (8781326983935657 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (197405961212919 / 256000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau1092 :
    Real.arctan (8781326983935657 / 23308332111831161 : ℝ) ≤
      (720601519159810012143 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau1091 :
    Real.arctan (8781326983935657 / 10000000000000000 : ℝ) ≤
      (2 * (720601519159810012143 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13308332111831161 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8781326983935657 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8781326983935657 / 10000000000000000 : ℝ) /
                (1 + (13308332111831161 / 10000000000000000 : ℝ)) =
              (8781326983935657 / 23308332111831161 : ℝ)
            by
        norm_num];
        exact hau1092)
  have hat1 :
    (Real.pi / 2 - (2 * (720601519159810012143 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8781326983935657 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8781326983935657 : ℝ) =
              (8781326983935657 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1091)
  have hz1 :
    (10000000000000000 / 8781326983935657 : ℝ) ≤
      1 / Real.sqrt (197405961212919 / 256000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8781326983935657 : ℝ) =
          1 / (8781326983935657 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1463554497322609 : ℝ) ≤
      (6656385480894487883 / 78125000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (197405961212919 / 256000000000000 : ℝ) ≤
      (125000000000000 / 1463554497322609 : ℝ) := by
    rw [show
        (125000000000000 / 1463554497322609 : ℝ) =
          (3 / 40) / (4390663491967827 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (720601519159810012143 / 2000000000000000000000 : ℝ))) -
        6 * (6656385480894487883 / 78125000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (197405961212919 / 256000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (197405961212919 / 256000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4390663491967827 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (720601519159810012143 / 2000000000000000000000 : ℝ))) -
          6 * (6656385480894487883 / 78125000000000000000 : ℝ))) ≤
      Real.sqrt (197405961212919 / 256000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (197405961212919 / 256000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (197405961212919 / 256000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
