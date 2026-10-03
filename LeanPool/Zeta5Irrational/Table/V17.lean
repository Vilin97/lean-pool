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

/-! # V17: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_205 :
    ((729973064772568471697 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9075704862963237331003 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3964718832390083 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3774612018114385332253 / 10000000000000000000000 : ℝ)) -
              6 * (1869593164174766211853 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (20120314137483 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20120314137483 / 128000000000000 : ℝ)) =
      Real.log (148120314137483 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20120314137483 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20840314137483 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (729973064772568471697 / 5000000000000000000000 : ℝ) ≤
      Real.log (148120314137483 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20840314137483 / 128000000000000 : ℝ) ≤
      (-(9075704862963237331003 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (20840314137483 / 128000000000000 : ℝ) = (20840314137483 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20840314137483 / 16000000000000 : ℝ) ≤
            (1321502841536762668997 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3964718832390083 / 10000000000000000 : ℝ) ≤
      Real.sqrt (20120314137483 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20120314137483 / 128000000000000 : ℝ) ≤
      (1982359416195043 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20120314137483 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau267 :
    Real.arctan (1982359416195043 / 5000000000000000 : ℝ) ≤
      (3774612018114385332253 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3774612018114385332253 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1982359416195043 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1982359416195043 : ℝ) =
              (1982359416195043 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau267)
  have hz1 :
    (5000000000000000 / 1982359416195043 : ℝ) ≤
      1 / Real.sqrt (20120314137483 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1982359416195043 : ℝ) = 1 / (1982359416195043 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3964718832390083 : ℝ) ≤
      (1869593164174766211853 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20120314137483 / 128000000000000 : ℝ) ≤
      (750000000000000 / 3964718832390083 : ℝ) := by
    rw [show
        (750000000000000 / 3964718832390083 : ℝ) =
          (3 / 40) / (3964718832390083 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3774612018114385332253 / 10000000000000000000000 : ℝ)) -
        6 * (1869593164174766211853 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20120314137483 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20120314137483 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3964718832390083 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3774612018114385332253 / 10000000000000000000000 : ℝ)) -
          6 * (1869593164174766211853 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (20120314137483 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20120314137483 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20120314137483 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_206 :
    ((1463778767588773677433 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18124201486317085329591 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((248144322472327 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3779442042935979217611 / 10000000000000000000000 : ℝ)) -
              6 * (373404301033048224383 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (10088547086377 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10088547086377 / 64000000000000 : ℝ)) =
      Real.log (74088547086377 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10088547086377 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10448547086377 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1463778767588773677433 / 10000000000000000000000 : ℝ) ≤
      Real.log (74088547086377 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10448547086377 / 64000000000000 : ℝ) ≤
      (-(18124201486317085329591 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (10448547086377 / 64000000000000 : ℝ) = (10448547086377 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10448547086377 / 8000000000000 : ℝ) ≤
            (2670213922682914670409 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (248144322472327 / 625000000000000 : ℝ) ≤ Real.sqrt (10088547086377 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10088547086377 / 64000000000000 : ℝ) ≤ (794061831911447 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10088547086377 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau268 :
    Real.arctan (794061831911447 / 2000000000000000 : ℝ) ≤
      (3779442042935979217611 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3779442042935979217611 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 794061831911447 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 794061831911447 : ℝ) =
              (794061831911447 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau268)
  have hz1 :
    (2000000000000000 / 794061831911447 : ℝ) ≤
      1 / Real.sqrt (10088547086377 / 64000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 794061831911447 : ℝ) = 1 / (794061831911447 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 248144322472327 : ℝ) ≤
      (373404301033048224383 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10088547086377 / 64000000000000 : ℝ) ≤
      (46875000000000 / 248144322472327 : ℝ) := by
    rw [show
        (46875000000000 / 248144322472327 : ℝ) =
          (3 / 40) / (248144322472327 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3779442042935979217611 / 10000000000000000000000 : ℝ)) -
        6 * (373404301033048224383 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10088547086377 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10088547086377 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((248144322472327 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3779442042935979217611 / 10000000000000000000000 : ℝ)) -
          6 * (373404301033048224383 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (10088547086377 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10088547086377 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10088547086377 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_207 :
    ((1467609937283719993659 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(226213338433879786221 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3975891626417843 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1892131714307245280953 / 5000000000000000000000 : ℝ)) -
              6 * (233057553786498956527 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (809354968321 / 5120000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (809354968321 / 5120000000000 : ℝ)) =
      Real.log (5929354968321 / 5120000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((809354968321 / 5120000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (838154968321 / 5120000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1467609937283719993659 / 10000000000000000000000 : ℝ) ≤
      Real.log (5929354968321 / 5120000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (838154968321 / 5120000000000 : ℝ) ≤
      (-(226213338433879786221 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (838154968321 / 5120000000000 : ℝ) = (838154968321 / 640000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (838154968321 / 640000000000 : ℝ) ≤
            (33716854178620213779 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3975891626417843 / 10000000000000000 : ℝ) ≤ Real.sqrt (809354968321 / 5120000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (809354968321 / 5120000000000 : ℝ) ≤ (1987945813208923 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (809354968321 / 5120000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau269 :
    Real.arctan (1987945813208923 / 5000000000000000 : ℝ) ≤
      (1892131714307245280953 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1892131714307245280953 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1987945813208923 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1987945813208923 : ℝ) =
              (1987945813208923 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau269)
  have hz1 :
    (5000000000000000 / 1987945813208923 : ℝ) ≤
      1 / Real.sqrt (809354968321 / 5120000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1987945813208923 : ℝ) = 1 / (1987945813208923 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3975891626417843 : ℝ) ≤
      (233057553786498956527 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (809354968321 / 5120000000000 : ℝ) ≤
      (750000000000000 / 3975891626417843 : ℝ) := by
    rw [show
        (750000000000000 / 3975891626417843 : ℝ) =
          (3 / 40) / (3975891626417843 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1892131714307245280953 / 5000000000000000000000 : ℝ)) -
        6 * (233057553786498956527 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (809354968321 / 5120000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (809354968321 / 5120000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3975891626417843 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1892131714307245280953 / 5000000000000000000000 : ℝ)) -
          6 * (233057553786498956527 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (809354968321 / 5120000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (809354968321 / 5120000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (809354968321 / 5120000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_208 :
    ((367859909938660910269 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2258750761441776246791 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1990733133017519 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (378907621031154650991 / 1000000000000000000000 : ℝ)) -
              6 * (1861909867144123045899 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (634082945103 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (634082945103 / 4000000000000 : ℝ)) =
      Real.log (4634082945103 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((634082945103 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (656582945103 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (367859909938660910269 / 2500000000000000000000 : ℝ) ≤
      Real.log (4634082945103 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (656582945103 / 4000000000000 : ℝ) ≤
      (-(2258750761441776246791 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (656582945103 / 4000000000000 : ℝ) = (656582945103 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (656582945103 / 500000000000 : ℝ) ≤
            (340551164683223753209 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1990733133017519 / 5000000000000000 : ℝ) ≤ Real.sqrt (634082945103 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (634082945103 / 4000000000000 : ℝ) ≤ (3981466266035041 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (634082945103 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau270 :
    Real.arctan (3981466266035041 / 10000000000000000 : ℝ) ≤
      (378907621031154650991 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (378907621031154650991 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3981466266035041 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3981466266035041 : ℝ) =
              (3981466266035041 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau270)
  have hz1 :
    (10000000000000000 / 3981466266035041 : ℝ) ≤
      1 / Real.sqrt (634082945103 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3981466266035041 : ℝ) =
          1 / (3981466266035041 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1990733133017519 : ℝ) ≤
      (1861909867144123045899 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (634082945103 / 4000000000000 : ℝ) ≤
      (375000000000000 / 1990733133017519 : ℝ) := by
    rw [show
        (375000000000000 / 1990733133017519 : ℝ) =
          (3 / 40) / (1990733133017519 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (378907621031154650991 / 1000000000000000000000 : ℝ)) -
        6 * (1861909867144123045899 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (634082945103 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (634082945103 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1990733133017519 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (378907621031154650991 / 1000000000000000000000 : ℝ)) -
          6 * (1861909867144123045899 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (634082945103 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (634082945103 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (634082945103 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_209 :
    ((1475267876124920720441 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18043018140451505241589 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((797406622248159 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3793880422948913718569 / 10000000000000000000000 : ℝ)) -
              6 * (1859369744002478350221 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (20347434278567 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20347434278567 / 128000000000000 : ℝ)) =
      Real.log (148347434278567 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20347434278567 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21067434278567 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1475267876124920720441 / 10000000000000000000000 : ℝ) ≤
      Real.log (148347434278567 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21067434278567 / 128000000000000 : ℝ) ≤
      (-(18043018140451505241589 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21067434278567 / 128000000000000 : ℝ) = (21067434278567 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21067434278567 / 16000000000000 : ℝ) ≤
            (2751397268548494758411 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (797406622248159 / 2000000000000000 : ℝ) ≤ Real.sqrt (20347434278567 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20347434278567 / 128000000000000 : ℝ) ≤
      (1993516555620399 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20347434278567 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau271 :
    Real.arctan (1993516555620399 / 5000000000000000 : ℝ) ≤
      (3793880422948913718569 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3793880422948913718569 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1993516555620399 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1993516555620399 : ℝ) =
              (1993516555620399 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau271)
  have hz1 :
    (5000000000000000 / 1993516555620399 : ℝ) ≤
      1 / Real.sqrt (20347434278567 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1993516555620399 : ℝ) = 1 / (1993516555620399 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 265802207416053 : ℝ) ≤
      (1859369744002478350221 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20347434278567 / 128000000000000 : ℝ) ≤
      (50000000000000 / 265802207416053 : ℝ) := by
    rw [show
        (50000000000000 / 265802207416053 : ℝ) =
          (3 / 40) / (797406622248159 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3793880422948913718569 / 10000000000000000000000 : ℝ)) -
        6 * (1859369744002478350221 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20347434278567 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20347434278567 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((797406622248159 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3793880422948913718569 / 10000000000000000000000 : ℝ)) -
          6 * (1859369744002478350221 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (20347434278567 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20347434278567 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20347434278567 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_210 :
    ((1479094647516637661407 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9008051414162736961301 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1996296097319103 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (474834512651351679093 / 1250000000000000000000 : ℝ)) -
              6 * (928419994915581758669 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (10202107156919 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10202107156919 / 64000000000000 : ℝ)) =
      Real.log (74202107156919 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10202107156919 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10562107156919 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1479094647516637661407 / 10000000000000000000000 : ℝ) ≤
      Real.log (74202107156919 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10562107156919 / 64000000000000 : ℝ) ≤
      (-(9008051414162736961301 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (10562107156919 / 64000000000000 : ℝ) = (10562107156919 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10562107156919 / 8000000000000 : ℝ) ≤
            (1389156290337263038699 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1996296097319103 / 5000000000000000 : ℝ) ≤ Real.sqrt (10202107156919 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10202107156919 / 64000000000000 : ℝ) ≤
      (3992592194638209 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10202107156919 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau272 :
    Real.arctan (3992592194638209 / 10000000000000000 : ℝ) ≤
      (474834512651351679093 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (474834512651351679093 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3992592194638209 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3992592194638209 : ℝ) =
              (3992592194638209 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau272)
  have hz1 :
    (10000000000000000 / 3992592194638209 : ℝ) ≤
      1 / Real.sqrt (10202107156919 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3992592194638209 : ℝ) =
          1 / (3992592194638209 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 665432032439701 : ℝ) ≤
      (928419994915581758669 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10202107156919 / 64000000000000 : ℝ) ≤
      (125000000000000 / 665432032439701 : ℝ) := by
    rw [show
        (125000000000000 / 665432032439701 : ℝ) =
          (3 / 40) / (1996296097319103 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (474834512651351679093 / 1250000000000000000000 : ℝ)) -
        6 * (928419994915581758669 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10202107156919 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10202107156919 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1996296097319103 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (474834512651351679093 / 1250000000000000000000 : ℝ)) -
          6 * (928419994915581758669 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (10202107156919 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10202107156919 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10202107156919 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_211 :
    ((11863359640404745567 / 80000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1798925976518522571577 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3998143548603701 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1901731639773101406791 / 5000000000000000000000 : ℝ)) -
              6 * (927160267134600840667 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (20460994349109 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20460994349109 / 128000000000000 : ℝ)) =
      Real.log (148460994349109 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20460994349109 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21180994349109 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (11863359640404745567 / 80000000000000000000 : ℝ) ≤
      Real.log (148460994349109 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21180994349109 / 128000000000000 : ℝ) ≤
      (-(1798925976518522571577 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21180994349109 / 128000000000000 : ℝ) = (21180994349109 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21180994349109 / 16000000000000 : ℝ) ≤
            (280515564381477428423 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3998143548603701 / 10000000000000000 : ℝ) ≤
      Real.sqrt (20460994349109 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20460994349109 / 128000000000000 : ℝ) ≤ (499767943575463 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20460994349109 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau273 :
    Real.arctan (499767943575463 / 1250000000000000 : ℝ) ≤
      (1901731639773101406791 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1901731639773101406791 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 499767943575463 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 499767943575463 : ℝ) =
              (499767943575463 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau273)
  have hz1 :
    (1250000000000000 / 499767943575463 : ℝ) ≤
      1 / Real.sqrt (20460994349109 / 128000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 499767943575463 : ℝ) = 1 / (499767943575463 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3998143548603701 : ℝ) ≤
      (927160267134600840667 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20460994349109 / 128000000000000 : ℝ) ≤
      (750000000000000 / 3998143548603701 : ℝ) := by
    rw [show
        (750000000000000 / 3998143548603701 : ℝ) =
          (3 / 40) / (3998143548603701 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1901731639773101406791 / 5000000000000000000000 : ℝ)) -
        6 * (927160267134600840667 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20460994349109 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20460994349109 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3998143548603701 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1901731639773101406791 / 5000000000000000000000 : ℝ)) -
          6 * (927160267134600840667 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (20460994349109 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20460994349109 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20460994349109 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_212 :
    ((185842974980787540947 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2245311070523984085901 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1000921801322313 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1904120996085517332403 / 5000000000000000000000 : ℝ)) -
              6 * (185181130762230820097 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (1025888719219 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1025888719219 / 6400000000000 : ℝ)) =
      Real.log (7425888719219 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1025888719219 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1061888719219 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (185842974980787540947 / 1250000000000000000000 : ℝ) ≤
      Real.log (7425888719219 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1061888719219 / 6400000000000 : ℝ) ≤
      (-(2245311070523984085901 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1061888719219 / 6400000000000 : ℝ) = (1061888719219 / 800000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1061888719219 / 800000000000 : ℝ) ≤
            (353990855601015914099 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1000921801322313 / 2500000000000000 : ℝ) ≤ Real.sqrt (1025888719219 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1025888719219 / 6400000000000 : ℝ) ≤ (800737441057851 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1025888719219 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau274 :
    Real.arctan (800737441057851 / 2000000000000000 : ℝ) ≤
      (1904120996085517332403 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1904120996085517332403 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 800737441057851 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 800737441057851 : ℝ) =
              (800737441057851 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau274)
  have hz1 :
    (2000000000000000 / 800737441057851 : ℝ) ≤
      1 / Real.sqrt (1025888719219 / 6400000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 800737441057851 : ℝ) = 1 / (800737441057851 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 333640600440771 : ℝ) ≤
      (185181130762230820097 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1025888719219 / 6400000000000 : ℝ) ≤
      (62500000000000 / 333640600440771 : ℝ) := by
    rw [show
        (62500000000000 / 333640600440771 : ℝ) =
          (3 / 40) / (1000921801322313 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1904120996085517332403 / 5000000000000000000000 : ℝ)) -
        6 * (185181130762230820097 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1025888719219 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1025888719219 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1000921801322313 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1904120996085517332403 / 5000000000000000000000 : ℝ)) -
          6 * (185181130762230820097 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (1025888719219 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1025888719219 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1025888719219 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_213 :
    ((372641545755497074473 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(896789442080253987649 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((801844639324909 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3813012273070485265727 / 10000000000000000000000 : ℝ)) -
              6 * (1849312240854789952491 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (20574554419651 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20574554419651 / 128000000000000 : ℝ)) =
      Real.log (148574554419651 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20574554419651 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21294554419651 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (372641545755497074473 / 2500000000000000000000 : ℝ) ≤
      Real.log (148574554419651 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21294554419651 / 128000000000000 : ℝ) ≤
      (-(896789442080253987649 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21294554419651 / 128000000000000 : ℝ) = (21294554419651 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21294554419651 / 16000000000000 : ℝ) ≤
            (142931328369746012351 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (801844639324909 / 2000000000000000 : ℝ) ≤ Real.sqrt (20574554419651 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20574554419651 / 128000000000000 : ℝ) ≤
      (1002305799156137 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20574554419651 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau275 :
    Real.arctan (1002305799156137 / 2500000000000000 : ℝ) ≤
      (3813012273070485265727 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3813012273070485265727 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1002305799156137 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1002305799156137 : ℝ) =
              (1002305799156137 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau275)
  have hz1 :
    (2500000000000000 / 1002305799156137 : ℝ) ≤
      1 / Real.sqrt (20574554419651 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1002305799156137 : ℝ) = 1 / (1002305799156137 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 801844639324909 : ℝ) ≤
      (1849312240854789952491 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20574554419651 / 128000000000000 : ℝ) ≤
      (150000000000000 / 801844639324909 : ℝ) := by
    rw [show
        (150000000000000 / 801844639324909 : ℝ) =
          (3 / 40) / (801844639324909 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3813012273070485265727 / 10000000000000000000000 : ℝ)) -
        6 * (1849312240854789952491 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20574554419651 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20574554419651 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((801844639324909 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3813012273070485265727 / 10000000000000000000000 : ℝ)) -
          6 * (1849312240854789952491 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (20574554419651 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20574554419651 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20574554419651 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_214 :
    ((747193552847302273959 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17909160216750060519991 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4014751554319121 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (763554831200230249377 / 2000000000000000000000 : ℝ)) -
              6 * (369364653116313286371 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (10315667227461 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10315667227461 / 64000000000000 : ℝ)) =
      Real.log (74315667227461 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10315667227461 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10675667227461 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (747193552847302273959 / 5000000000000000000000 : ℝ) ≤
      Real.log (74315667227461 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10675667227461 / 64000000000000 : ℝ) ≤
      (-(17909160216750060519991 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (10675667227461 / 64000000000000 : ℝ) = (10675667227461 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10675667227461 / 8000000000000 : ℝ) ≤
            (2885255192249939480009 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4014751554319121 / 10000000000000000 : ℝ) ≤
      Real.sqrt (10315667227461 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10315667227461 / 64000000000000 : ℝ) ≤ (1003687888579781 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10315667227461 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau276 :
    Real.arctan (1003687888579781 / 2500000000000000 : ℝ) ≤
      (763554831200230249377 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (763554831200230249377 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1003687888579781 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1003687888579781 : ℝ) =
              (1003687888579781 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau276)
  have hz1 :
    (2500000000000000 / 1003687888579781 : ℝ) ≤
      1 / Real.sqrt (10315667227461 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1003687888579781 : ℝ) = 1 / (1003687888579781 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4014751554319121 : ℝ) ≤
      (369364653116313286371 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10315667227461 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4014751554319121 : ℝ) := by
    rw [show
        (750000000000000 / 4014751554319121 : ℝ) =
          (3 / 40) / (4014751554319121 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (763554831200230249377 / 2000000000000000000000 : ℝ)) -
        6 * (369364653116313286371 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10315667227461 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10315667227461 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4014751554319121 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (763554831200230249377 / 2000000000000000000000 : ℝ)) -
          6 * (369364653116313286371 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (10315667227461 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10315667227461 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10315667227461 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_215 :
    ((1498206568979816676777 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17882602311985011388837 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4020272309864503 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (29863497456978361057 / 78125000000000000000 : ℝ)) -
              6 * (461086078515075774277 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (20688114490193 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20688114490193 / 128000000000000 : ℝ)) =
      Real.log (148688114490193 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20688114490193 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21408114490193 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1498206568979816676777 / 10000000000000000000000 : ℝ) ≤
      Real.log (148688114490193 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21408114490193 / 128000000000000 : ℝ) ≤
      (-(17882602311985011388837 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (21408114490193 / 128000000000000 : ℝ) = (21408114490193 / 16000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21408114490193 / 16000000000000 : ℝ) ≤
            (2911813097014988611163 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4020272309864503 / 10000000000000000 : ℝ) ≤
      Real.sqrt (20688114490193 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20688114490193 / 128000000000000 : ℝ) ≤
      (2010136154932253 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20688114490193 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau277 :
    Real.arctan (2010136154932253 / 5000000000000000 : ℝ) ≤
      (29863497456978361057 / 78125000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (29863497456978361057 / 78125000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2010136154932253 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2010136154932253 : ℝ) =
              (2010136154932253 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau277)
  have hz1 :
    (5000000000000000 / 2010136154932253 : ℝ) ≤
      1 / Real.sqrt (20688114490193 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2010136154932253 : ℝ) = 1 / (2010136154932253 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4020272309864503 : ℝ) ≤
      (461086078515075774277 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20688114490193 / 128000000000000 : ℝ) ≤
      (750000000000000 / 4020272309864503 : ℝ) := by
    rw [show
        (750000000000000 / 4020272309864503 : ℝ) =
          (3 / 40) / (4020272309864503 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (29863497456978361057 / 78125000000000000000 : ℝ)) -
        6 * (461086078515075774277 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20688114490193 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20688114490193 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4020272309864503 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (29863497456978361057 / 78125000000000000000 : ℝ)) -
          6 * (461086078515075774277 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (20688114490193 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20688114490193 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20688114490193 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_216 :
    ((300404914798402879239 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17856114752668976953491 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2012892747268141 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (382727286185266192809 / 1000000000000000000000 : ℝ)) -
              6 * (460468829795916814311 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2593111815683 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2593111815683 / 16000000000000 : ℝ)) =
      Real.log (18593111815683 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2593111815683 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2683111815683 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (300404914798402879239 / 2000000000000000000000 : ℝ) ≤
      Real.log (18593111815683 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2683111815683 / 16000000000000 : ℝ) ≤
      (-(17856114752668976953491 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2683111815683 / 16000000000000 : ℝ) = (2683111815683 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2683111815683 / 2000000000000 : ℝ) ≤
            (2938300656331023046509 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2012892747268141 / 5000000000000000 : ℝ) ≤ Real.sqrt (2593111815683 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2593111815683 / 16000000000000 : ℝ) ≤ (805157098907257 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2593111815683 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau278 :
    Real.arctan (805157098907257 / 2000000000000000 : ℝ) ≤
      (382727286185266192809 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (382727286185266192809 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 805157098907257 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 805157098907257 : ℝ) =
              (805157098907257 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau278)
  have hz1 :
    (2000000000000000 / 805157098907257 : ℝ) ≤
      1 / Real.sqrt (2593111815683 / 16000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 805157098907257 : ℝ) = 1 / (805157098907257 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2012892747268141 : ℝ) ≤
      (460468829795916814311 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2593111815683 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2012892747268141 : ℝ) := by
    rw [show
        (375000000000000 / 2012892747268141 : ℝ) =
          (3 / 40) / (2012892747268141 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (382727286185266192809 / 1000000000000000000000 : ℝ)) -
        6 * (460468829795916814311 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2593111815683 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2593111815683 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2012892747268141 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (382727286185266192809 / 1000000000000000000000 : ℝ)) -
          6 * (460468829795916814311 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (2593111815683 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2593111815683 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2593111815683 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
