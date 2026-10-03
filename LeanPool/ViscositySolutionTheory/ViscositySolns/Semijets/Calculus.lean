/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Calculus.ShiftsClosedness

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Semijet calculus

This file contains calculus lemmas for second-order superjets and subjets:
addition, convexity, shifts, Hessian monotonicity, fixed-gradient Hessian
slice closedness, and negation duality. The development lives in the
`Calculus/` submodules; this file re-exports all of them.
-/

@[expose] public section
