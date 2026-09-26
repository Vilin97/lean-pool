/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-! # Exact scalar threshold identities for the auxiliary nonstandard route -/

@[expose] public section

namespace QuadraticCarleson


theorem sqrt_mul_threshold_rpow {a w p : ℝ}
    (ha : 0 < a) (hw : 0 < w) (hp : 0 < p) :
    Real.sqrt w * (a * w ^ (-1 / p)) ^ (1 - p / 2) =
      a ^ (1 - p / 2) * w ^ ((p - 1) / p) := by
  rw [Real.sqrt_eq_rpow,
    Real.mul_rpow ha.le (Real.rpow_nonneg hw.le _), ← Real.rpow_mul hw.le,
    mul_left_comm, ← Real.rpow_add hw]
  have he : (1 / 2 : ℝ) + (-1 / p) * (1 - p / 2) = (p - 1) / p := by
    field_simp
    ring
  rw [he]


theorem positive_threshold_rpow_one_sub {a w p : ℝ}
    (ha : 0 < a) (hw : 0 < w) (hp : 0 < p) :
    (a * w ^ (-1 / p)) ^ (1 - p) =
      a ^ (1 - p) * w ^ ((p - 1) / p) := by
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hw.le _), ← Real.rpow_mul hw.le]
  have he : (-1 / p) * (1 - p) = (p - 1) / p := by
    field_simp
    ring
  rw [he]


theorem reciprocal_holder_quotient (p : ℝ) :
    1 / (p / (p - 1)) = (p - 1) / p :=
  one_div_div (a := p) (b := p - 1)


end QuadraticCarleson
