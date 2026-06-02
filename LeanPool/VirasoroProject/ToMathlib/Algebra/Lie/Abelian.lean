/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Lie.Abelian

/-!
# LeanPool.VirasoroProject.ToMathlib.Algebra.Lie.Abelian
-/

instance _root_.CommRing.isLieAbelian (R : Type*) [CommRing R] : IsLieAbelian R where
  trivial c₁ c₂ := by
    change c₁ * c₂ - c₂ * c₁ = 0
    simp [mul_comm]
