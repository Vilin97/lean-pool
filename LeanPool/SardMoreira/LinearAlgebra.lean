/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

open Function
open Module (finrank)

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]
  [AddCommGroup H] [Module ℝ H]


namespace LinearMap

theorem rank_prod_fst (f : E × F →ₗ[ℝ] G) :
    rank (prod (fst ℝ E F) f) = (Module.rank ℝ E).lift + (f ∘ₗ inr ℝ E F).rank.lift := by
  -- The range of the product map is isomorphic
  -- to the direct sum of the ranges of the first projection and the function f.
  have h_range : range (prod (fst ℝ E F) f) ≃ₗ[ℝ] E × range (f ∘ₗ (inr ℝ E F)) := by
    refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩;
    · refine prod (fst ℝ _ _ ∘ₗ Submodule.subtype _)
        (codRestrict _ ((snd _ _ _ - f ∘ₗ inl _ _ _ ∘ₗ fst _ _ _) ∘ₗ Submodule.subtype _) ?_)
      rintro ⟨_, ⟨x, y⟩, rfl⟩
      simp [← map_sub]
    · rintro ⟨_, ⟨x, y⟩, rfl⟩ ⟨_, ⟨x', y'⟩, rfl⟩ h
      obtain rfl : x = x' := by simpa using congr($h |>.1)
      simp_all [← Subtype.val_inj]
    · rintro ⟨x, _, y, rfl⟩
      refine ⟨⟨_, (x, y), rfl⟩, ?_⟩
      simp [← Subtype.val_inj, ← map_sub]
  simpa using h_range.lift_rank_eq

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem finrank_range_prod_fst (f : E × F →ₗ[ℝ] G) :
    finrank ℝ (range <| prod (fst ℝ E F) f) =
      Module.finrank ℝ E + finrank ℝ (range <| f ∘ₗ inr ℝ E F) := by
  rw [Module.finrank, ← LinearMap.rank, rank_prod_fst, Cardinal.toNat_add] <;>
    simp [finrank, Module.rank_lt_aleph0]

theorem finrank_range_prod_fst_iff_comp_inr_eq_zero (f : E × F →ₗ[ℝ] G) :
    finrank ℝ (range (prod (fst ℝ E F) f)) = finrank ℝ E ↔ f ∘ₗ inr ℝ E F = 0 := by
  simp [finrank_range_prod_fst, range_eq_bot]

end LinearMap
