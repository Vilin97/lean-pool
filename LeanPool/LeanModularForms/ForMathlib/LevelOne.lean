/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import LeanPool.LeanModularForms.ForMathlib.QExpansion
import LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps
import LeanPool.LeanModularForms.ForMathlib.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite-dimensionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic

local notation "𝕢" => qParam

