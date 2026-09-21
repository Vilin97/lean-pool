/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.RearrangementNumber.NonMRR.Main

/-!
# Proved Palomar declarations

These declarations discharge the three statements in `Challenge.lean` using
the substantive proof development in this repository. Challenge and Solution
are separate environments: never import Challenge here.
-/

open Cardinal

namespace PalomarRR

/-- The real nonmeagre minimum exists by the Baire category theorem. -/
theorem nonM_minimum :
    ∃ s : Set ℝ, ¬ IsMeagre s ∧ Cardinal.mk s = NonMRR.nonM := by
  exact NonMRR.exists_nonmeagre_minimizer ℝ

/-- Rearranging families exist and their cardinal minimum is attained. -/
theorem rr_minimum :
    ∃ P : Set (Equiv.Perm ℕ), NonMRR.IsRearranging P ∧ #P = NonMRR.rr := by
  exact NonMRR.exists_rearranging_family_of_cardinal_rr

/-- The lower-bound direction of the manuscript's Main Theorem 1.2. -/
theorem nonM_le_rr : NonMRR.nonM ≤ NonMRR.rr := by
  exact NonMRR.nonM_le_rr

end PalomarRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
