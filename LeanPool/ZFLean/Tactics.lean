/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import Mathlib.CategoryTheory.Category.Basic

/-!
# LeanPool.ZFLean.Tactics

Imported Lean Pool material for `LeanPool.ZFLean.Tactics`.
-/
/-- Imported ZFLean declaration. -/
register_label_attr zrel
/-- Imported ZFLean declaration. -/
register_label_attr zpfun
/-- Imported ZFLean declaration. -/
register_label_attr zfun

/-!
Thanks to Ghilain for the idea of registering specific attributes.
-/
namespace ZFTactics
/-- Imported ZFLean declaration. -/
macro "zrel" : tactic => do
  let zrel := Lean.mkIdent `zrel
  let zpfun := Lean.mkIdent `zpfun
  let zfun := Lean.mkIdent `zfun
  `(tactic| solve_by_elim using $zrel, $zpfun, $zfun)
/-- Imported ZFLean declaration. -/
macro "zpfun" : tactic => do
  let zpfun := Lean.mkIdent `zpfun
  let zfun := Lean.mkIdent `zfun
  `(tactic| solve_by_elim using $zpfun, $zfun)
/-- Imported ZFLean declaration. -/
macro "zfun" : tactic => do
  let zfun := Lean.mkIdent `zfun
  `(tactic| solve_by_elim using $zfun)

end ZFTactics
