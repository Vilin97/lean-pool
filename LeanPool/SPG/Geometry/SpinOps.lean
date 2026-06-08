/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Data.Matrix.Basic

/-!
# Spin operation matrices

This module provides the rational `3 × 3` matrices for the spin identity and
spin reversal (time-reversal) operations.
-/

namespace SPG.Geometry.SpinOps

/-- Spin I. -/
def spinI : Matrix (Fin 3) (Fin 3) ℚ :=
  1

/-- Spin Neg I. -/
def spinNegI : Matrix (Fin 3) (Fin 3) ℚ :=
  -1

end SPG.Geometry.SpinOps
