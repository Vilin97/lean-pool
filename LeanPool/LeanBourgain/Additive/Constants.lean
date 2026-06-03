/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Quantitative constants for the additive combinatorics core

The constants `fullC₂ β` and `fullC β` track the explicit dependence on a
doubling parameter `β` in the additive-combinatorics core of the Bourgain
extractor proof.
-/

namespace LeanPool.LeanBourgain

/-- The auxiliary additive constant `fullC₂ β`. -/
noncomputable def fullC₂ (β : ℝ) : ℕ := 374 ^ ⌈Real.logb (3 / 2 : ℝ) (1 / β)⌉₊

/-- The full additive constant `fullC β` used in the Bourgain extractor estimates. -/
noncomputable def fullC (β : ℝ) : ℕ := (fullC₂ β) * 9

end LeanPool.LeanBourgain
