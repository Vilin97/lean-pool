/-
Copyright (c) 2026 Riccardo Brasca, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Pietro Monticone
-/

import LeanPool.QuadraticIntegers.Mathlib

/-!
# Quadratic Integers

Source: url:https://github.com/pitmonticone/QuadraticIntegers
Authors: Riccardo Brasca, Pietro Monticone
Status: verified
Main declarations: `LeanPool.QuadraticIntegers.Mathlib.QuadraticAlgebra.instAlgebraBaseChange`
Tags: number-theory, quadratic-fields, quadratic-algebras
MSC: 11R04, 11R11
-/

/-!
## Mathematical overview

The imported completed component supplies base-change algebra instances for
Mathlib's `QuadraticAlgebra`, used by the Quadratic Integers project to compare
orders such as `ℤ[√d]` with their scalar extensions.

The source repository also contains blueprint statements for the ring of
integers of a quadratic field, but those Lean files still contain unresolved
proof placeholders upstream and are not committed here.
-/
