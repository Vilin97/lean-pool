/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliAssembly

/-! The scalar normalization used by the centered Caccioppoli estimate. -/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

theorem caccioppoli_centered_rhs_eq
    {C r a b : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal C * ENNReal.ofReal (r * a ^ 2) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (r * b ^ 2) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (r ^ 2) ^ (1 / 6 : ℝ) =
      ENNReal.ofReal (C * r ^ (4 / 3 : ℝ) * a * b) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hr.le (sq_nonneg _)) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hr.le (sq_nonneg _)) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r) (by norm_num)]
  rw [Real.mul_rpow hr.le (sq_nonneg _), Real.mul_rpow hr.le (sq_nonneg _)]
  have ha' : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
    calc
      (a ^ 2) ^ (1 / 2 : ℝ) = (a ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (Real.rpow_natCast a 2).symm
      _ = a ^ ((2 : ℝ) * (1 / 2 : ℝ)) := by rw [Real.rpow_mul ha]
      _ = a := by norm_num
  have hb' : (b ^ 2) ^ (1 / 2 : ℝ) = b := by
    calc
      (b ^ 2) ^ (1 / 2 : ℝ) = (b ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (Real.rpow_natCast b 2).symm
      _ = b ^ ((2 : ℝ) * (1 / 2 : ℝ)) := by rw [Real.rpow_mul hb]
      _ = b := by norm_num
  have hrpow : (r ^ 2) ^ (1 / 6 : ℝ) = r ^ (1 / 3 : ℝ) := by
    calc
      (r ^ 2) ^ (1 / 6 : ℝ) = (r ^ (2 : ℝ)) ^ (1 / 6 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 6 : ℝ))
          (Real.rpow_natCast r 2).symm
      _ = r ^ ((2 : ℝ) * (1 / 6 : ℝ)) := by rw [Real.rpow_mul hr.le]
      _ = r ^ (1 / 3 : ℝ) := by norm_num
  rw [ha', hb', hrpow]
  rw [← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    C * (r ^ (1 / 2 : ℝ) * a) * (r ^ (1 / 2 : ℝ) * b) * r ^ (1 / 3 : ℝ) =
        C * (r ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) * r ^ (1 / 3 : ℝ) * a * b) := by
          ring
    _ = C * r ^ (4 / 3 : ℝ) * a * b := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr]
      norm_num
      ring

end CKN
