/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fintype.Parity


/- This is from the Sphere Pack project, so might not actually be for mathlib.-/

-- Probably put it at LinearAlgebra/Matrix/SpecialLinearGroup.lean

/-! # UpperHalfPlane -/


theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  simp only [S, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp
