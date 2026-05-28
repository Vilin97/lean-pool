/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.LinearAlgebra.Basis.Defs

/-- Standard basis of the space of finitely supported functions. -/
noncomputable def Finsupp.basisFun (X R : Type*) [Semiring R] : Module.Basis X R (X →₀ R) where
  repr := (LinearEquiv.refl _ _)
