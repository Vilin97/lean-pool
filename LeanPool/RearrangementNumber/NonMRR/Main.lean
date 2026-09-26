/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.CategoryBound
public import LeanPool.RearrangementNumber.NonMRR.RiemannBaire

/-!
# The uniformity of the meagre ideal is at most the rearrangement number

Both cardinals have their literal definitions: `nonM` uses nonmeagre subsets
of the real line, and `rr` uses rearranging families of permutations of ℕ.
All preceding construction and category lemmas have been proved over mathlib.
-/

@[expose] public section

open Cardinal

namespace NonMRR

/-- The defining minimum of the rearrangement number has an actual witness. -/
theorem exists_rearranging_family_of_cardinal_rr :
    ∃ P : Set (Equiv.Perm ℕ), IsRearranging P ∧ #P = rr := by
  have hnonempty : {κ : Cardinal |
      ∃ P : Set (Equiv.Perm ℕ), IsRearranging P ∧ #P = κ}.Nonempty :=
    ⟨#(Set.univ : Set (Equiv.Perm ℕ)), Set.univ, isRearranging_univ, rfl⟩
  exact csInf_mem hnonempty

/-- The uniformity of the meagre ideal on the real line is at most the
rearrangement number. There are no additional hypotheses. -/
theorem nonM_le_rr : nonM ≤ rr := by
  obtain ⟨P, hP, hcard⟩ := exists_rearranging_family_of_cardinal_rr
  exact (nonM_le_cardinal_of_isRearranging hP).trans_eq hcard

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
