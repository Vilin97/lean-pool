/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ScalarTrace

/-!
# The faithfulness trick

An element of the group algebra that kills every simple submodule
of the regular module is zero: by Maschke the regular module is a
supremum of simple submodules, so `1` decomposes as a finite sum
of elements of simples, and left multiplication kills each
summand.
-/

@[expose] public section

namespace RS

open Finset

variable {G : Type*}

/-- **The faithfulness trick**: killing every simple submodule of
the regular module forces vanishing. -/
theorem eq_zero_of_kills_simples [Group G] [Finite G]
    (x : MonoidAlgebra ℂ G)
    (hx : ∀ S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) S →
      ∀ s ∈ S, x * s = 0) :
    x = 0 := by
  classical
  let := Fintype.ofFinite G
  have : NeZero ((Nat.card G : ℂ)) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero⟩
  have htop := IsSemisimpleModule.sSup_simples_eq_top
    (R := MonoidAlgebra ℂ G) (M := MonoidAlgebra ℂ G)
  have h1 : (1 : MonoidAlgebra ℂ G) ∈
      sSup {m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) |
        IsSimpleModule (MonoidAlgebra ℂ G) m} := by
    rw [htop]
    trivial
  rw [sSup_eq_iSup'] at h1
  rw [Submodule.mem_iSup_iff_exists_finsupp] at h1
  obtain ⟨f, hf, hsum⟩ := h1
  have hx1 : x * 1 = 0 := by
    rw [← hsum]
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun S _ => ?_
    exact hx S.1 S.2 (f S) (hf S)
  rw [mul_one] at hx1
  exact hx1

end RS
