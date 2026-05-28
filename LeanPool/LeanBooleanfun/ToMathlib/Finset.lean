/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Auxiliary `Finset` lemmas

Small helper lemmas about `Finset` that are not specific to Boolean functions.
-/

namespace Finset

variable {α : Type*}

section ToDataFintypeBasic

variable [Fintype α] [DecidableEq α]

@[simp]
lemma filter_univ_not_mem (s : Finset α) : univ.filter (· ∉ s) = sᶜ := by
  ext; simp only [mem_filter, mem_univ, true_and, mem_compl]

end ToDataFintypeBasic

end Finset
