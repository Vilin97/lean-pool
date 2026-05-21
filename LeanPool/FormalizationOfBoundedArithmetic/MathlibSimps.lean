/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- In this file this is crucial to be careful with imports,
-- as all `simp` lemmas in scope will get our `delta0_simp` attribute!
import Lean
import Mathlib.Lean.Meta.Simp
import Mathlib.Tactic.Simps.Basic

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Complexity

import LeanPool.FormalizationOfBoundedArithmetic.Register

open Lean Elab Command

/-- Add existing Mathlib model-theory simp lemmas to the local `delta0_simps` simp set. -/
elab "mkDelta0FromModelTheory" : command => do
  let env ← getEnv
  let targetMod : Name := `FirstOrder.Language
  -- Collect all decls with names under the target module *and* having `[simp]`
  for (declName, _) in env.constants do
    if targetMod.isPrefixOf declName then
      if ← liftCoreM <| Meta.isInSimpSet `simp declName then
        elabCommand (← `(attribute [delta0_simps] $(mkIdent declName)))

mkDelta0FromModelTheory
