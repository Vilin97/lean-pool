/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams

/-!
# Single-box interpolation for Young diagrams

Given `lam ≤ mu` with `lam.card < mu.card`, we produce `nu` satisfying
`lam ≤ nu ≤ mu` and `nu.card = lam.card + 1`.  The idea is to pick a
cell in `mu.cells \ lam.cells` that is minimal for the sum of
coordinates, then insert it into `lam`.
-/

namespace RS

open Finset in
/-- **Single-box interpolation**: a strictly larger diagram can be
reached one cell at a time. -/
theorem exists_intermediate_diagram {lam mu : YoungDiagram}
    (hle : lam ≤ mu) (hlt : lam.card < mu.card) :
    ∃ nu : YoungDiagram, lam ≤ nu ∧ nu ≤ mu ∧ nu.card = lam.card + 1 := by
  -- The difference mu.cells \ lam.cells is nonempty
  have hdiff : (mu.cells \ lam.cells).Nonempty :=
    sdiff_nonempty_of_card_lt_card hlt
  -- Pick c in the difference minimizing c.1 + c.2
  obtain ⟨c, hc_mem, hc_min⟩ :=
    (mu.cells \ lam.cells).exists_min_image (fun c => c.1 + c.2) hdiff
  rw [mem_sdiff] at hc_mem
  obtain ⟨hc_mu, hc_nlam⟩ := hc_mem
  -- Build nu
  refine ⟨⟨insert c lam.cells, ?_⟩, ?_, ?_, ?_⟩
  · -- isLowerSet (∀ ⦃a b⦄, b ≤ a → a ∈ s → b ∈ s): insert c lam.cells is a
    --   lower set
    intro a b hba hmem_a
    simp only [Finset.mem_coe, Finset.mem_insert] at hmem_a ⊢
    -- a is in the set, b ≤ a, show b is in the set
    rcases hmem_a with rfl | hlam_a
    · -- a = c (after rfl, c is replaced by a); show b ∈ insert a lam.cells
      -- hba : b ≤ a, hc_mu : a ∈ mu (c was replaced by a)
      by_cases heq : b = a
      · exact Or.inl heq
      · -- b ≠ a, and b ≤ a componentwise
        right
        -- b ∈ mu by mu's lower-set property
        have hb_mu : (b : ℕ × ℕ) ∈ mu := mu.isLowerSet hba hc_mu
        -- If b ∉ lam, it would be in the difference with smaller sum,
        --   contradicting minimality
        by_contra hb_nlam
        have hb_diff : b ∈ mu.cells \ lam.cells :=
          mem_sdiff.mpr ⟨hb_mu, hb_nlam⟩
        -- hc_min (with c replaced by a): a.1 + a.2 ≤ b.1 + b.2
        have hle_sum : a.1 + a.2 ≤ b.1 + b.2 := hc_min b hb_diff
        have hb1 : b.1 ≤ a.1 := (Prod.le_def.mp hba).1
        have hb2 : b.2 ≤ a.2 := (Prod.le_def.mp hba).2
        exact heq (Prod.ext (le_antisymm hb1 (by omega)) (le_antisymm hb2 (by
          omega)))
    · -- a is in lam; use lam's lower-set property
      exact Or.inr (lam.isLowerSet hba hlam_a)
  · -- lam ≤ nu: lam.cells ⊆ insert c lam.cells
    intro x hx
    change x ∈ (insert c lam.cells : Finset _)
    exact mem_insert.mpr (Or.inr hx)
  · -- nu ≤ mu: insert c lam.cells ⊆ mu.cells
    intro x hx
    have hx' : x ∈ (insert c lam.cells : Finset _) := hx
    rcases mem_insert.mp hx' with rfl | hlam
    · exact hc_mu
    · exact hle hlam
  · -- nu.card = lam.card + 1
    change (insert c lam.cells).card = lam.cells.card + 1
    exact card_insert_of_notMem hc_nlam

end RS
