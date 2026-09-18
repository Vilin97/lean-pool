/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# LeanPool.VirasoroProject.ToMathlib.LinearAlgebra.Basis.Defs
-/

@[expose] public section

/-- Standard basis of the space of finitely supported functions. -/
noncomputable def Finsupp.basisFun (X R : Type*) [Semiring R] : Module.Basis X R (X →₀ R) where
  repr := (LinearEquiv.refl _ _)
