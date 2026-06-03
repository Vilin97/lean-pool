/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.Fintype.Parity

/-! # ForMathlibUpperHalfPlane -/


@[expose] public section

-- Probably put it at LinearAlgebra/Matrix/SpecialLinearGroup.lean

theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  simp only [S, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp
