/-
Copyright (c) 2026 Mary Jane. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mary Jane
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

elab "mkDelta0FromModelTheory" : command => do
  let targetMod : Name := `FirstOrder.Language
  -- Collect all declarations under the target module that currently have `[simp]`.
  for declName in ← liftCoreM <| Lean.Meta.getAllSimpDecls `simp do
    if targetMod.isPrefixOf declName then
      elabCommand (← `(attribute [delta0_simps] $(mkIdent declName)))

mkDelta0FromModelTheory
