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
  apply Subtype.ext
  change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; 1, 0] = -1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply]
