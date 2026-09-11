/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.NumberTheory.Modular
public import LeanPool.LeanModularForms.ForMathlib.QExpansion
public import LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps
public import LeanPool.LeanModularForms.ForMathlib.Identities
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite-dimensionality of these spaces of modular forms.

-/

@[expose] public section

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic

local notation "𝕢" => qParam

