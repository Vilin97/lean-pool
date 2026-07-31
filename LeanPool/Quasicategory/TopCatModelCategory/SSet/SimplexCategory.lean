/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory Simplicial

namespace SimplexCategory

lemma surjective_const {n : ℕ} (f : mk 0 ⟶ mk n) :
    ∃ (i : Fin (n + 1)), f = const ⦋0⦌ ⦋n⦌ i :=
  ⟨f.toOrderHom 0, by
    ext j
    fin_cases j
    rfl⟩

instance : Balanced SimplexCategory where
  isIso_of_mono_of_epi f h₁ h₂ := by
    rw [mono_iff_injective] at h₁
    rw [epi_iff_surjective] at h₂
    exact SimplexCategory.isIso_of_bijective ⟨h₁, h₂⟩

instance (n : SimplexCategory) (f : mk 0 ⟶ n) : IsSplitMono f where
  exists_splitMono := ⟨{ retraction := const _ _ 0 }⟩

instance {α β : Type*} [Preorder α] [Preorder β]
    [Finite α] [Finite β] : Finite (α →o β) :=
  Finite.of_injective (β := α → β) (fun f ↦ f) (fun f g h ↦ by
    ext x
    exact congr_fun h x)

instance (a b : SimplexCategory) : Finite (a ⟶ b) :=
  Finite.of_injective (β := Fin (a.len + 1) →o Fin (b.len + 1))
    (fun f ↦ f.toOrderHom) (fun f g h ↦ by
      ext x
      dsimp at h
      rw [h])

end SimplexCategory
