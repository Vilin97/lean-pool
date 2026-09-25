/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeTable

/-!
# Every simple module embeds in the regular module

Every simple `ℂ[G]`-module is isomorphic (as a module) to a simple
submodule of the regular module `MonoidAlgebra ℂ G`.
-/

namespace RS

open LinearMap

variable {G : Type*}

/-- Every simple `ℂ[G]`-module is isomorphic to a simple submodule
of the regular module. -/
theorem exists_simple_submodule_linearEquiv [Group G] [Finite G]
    (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    (hM : IsSimpleModule (MonoidAlgebra ℂ G) M) :
    ∃ S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) S ∧
      Nonempty (S ≃ₗ[MonoidAlgebra ℂ G] M) := by
  classical
  let := Fintype.ofFinite G
  -- Pick a nonzero element m : M.
  have := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  -- The map φ : MonoidAlgebra ℂ G →ₗ[MonoidAlgebra ℂ G] M, x ↦ x • m.
  let φ : MonoidAlgebra ℂ G →ₗ[MonoidAlgebra ℂ G] M :=
    LinearMap.toSpanSingleton (MonoidAlgebra ℂ G) M m
  -- φ is surjective: its range is a nonzero submodule of the simple M, hence ⊤.
  have hφ_surj : Function.Surjective φ := by
    rw [← range_eq_top]
    have hne : range φ ≠ ⊥ := by
      rw [ne_eq, eq_bot_iff]
      intro h
      have h1 : φ 1 ∈ range φ := mem_range_self φ 1
      have h1bot := h h1
      rw [Submodule.mem_bot] at h1bot
      simp? [φ, toSpanSingleton, smulRight] at h1bot
      exact hm h1bot
    rcases hM.eq_bot_or_eq_top (range φ) with h | h
    · exact absurd h hne
    · exact h
  -- The kernel K := ker φ.
  let K := ker φ
  -- By Maschke / semisimplicity, K has a complement S.
  have : NeZero ((Nat.card G : ℂ)) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero⟩
  have : IsSemisimpleModule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)
    := inferInstance
  obtain ⟨S, hcompl⟩ := exists_isCompl K
  -- Build the linear equivalence S ≃ₗ M.
  let e₁ : (MonoidAlgebra ℂ G ⧸ K) ≃ₗ[MonoidAlgebra ℂ G] M :=
    φ.quotKerEquivOfSurjective hφ_surj
  let e₂ : (MonoidAlgebra ℂ G ⧸ K) ≃ₗ[MonoidAlgebra ℂ G] S :=
    Submodule.quotientEquivOfIsCompl K S hcompl
  let e : S ≃ₗ[MonoidAlgebra ℂ G] M := e₂.symm.trans e₁
  -- S is simple because it is linearly equivalent to the simple module M.
  have hS : IsSimpleModule (MonoidAlgebra ℂ G) S :=
    IsSimpleModule.congr e
  exact ⟨S, hS, ⟨e⟩⟩

end RS
