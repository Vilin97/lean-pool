/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Quantitative constants for the additive combinatorics core

The constants `full_C₂ β` and `full_C β` track the explicit dependence on a
doubling parameter `β` in the additive-combinatorics core of the Bourgain
extractor proof.
-/

namespace LeanPool.LeanBourgain

/-- The auxiliary additive constant `full_C₂ β`. -/
noncomputable def full_C₂ (β : ℝ) : ℕ := 374 ^ ⌈Real.logb (3 / 2 : ℝ) (1 / β)⌉₊

/-- The full additive constant `full_C β` used in the Bourgain extractor estimates. -/
noncomputable def full_C (β : ℝ) : ℕ := (full_C₂ β) * 9

end LeanPool.LeanBourgain
