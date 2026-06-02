/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.Tactic.FunProp

public import LeanPool.LeanModularForms.Modularforms.Eisenstein

/-! # MDifferentiableFunProp -/


@[expose] public section

open scoped Manifold UpperHalfPlane EisensteinSeries

theorem E₄_MDifferentiable : MDiff E₄.toFun := E₄.holo'

theorem E₆_MDifferentiable : MDiff E₆.toFun := E₆.holo'

/-
Register `MDifferentiable` as a `fun_prop` so that we can use it in `fun_prop`-based proofs.
To be upstreamed in mathlib PR [#33808](https://github.com/leanprover-community/mathlib4/pull/33808)
-/
attribute [fun_prop] MDifferentiable

attribute [fun_prop]
  MDifferentiable.add
  MDifferentiable.sub
  MDifferentiable.neg
  MDifferentiable.mul
  MDifferentiable.pow
  MDifferentiable.const_smul
  mdifferentiable_const
  E₄_MDifferentiable
  E₆_MDifferentiable
