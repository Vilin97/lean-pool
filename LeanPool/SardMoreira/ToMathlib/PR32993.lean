/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Basic

/-!
# LeanPool.SardMoreira.ToMathlib.PR32993
-/

@[expose] public section

open ENNReal

protected theorem ENNReal.div_right_comm {a b c : ℝ≥0∞} : a / b / c = a / c / b := by
  simp only [div_eq_mul_inv, mul_right_comm]
