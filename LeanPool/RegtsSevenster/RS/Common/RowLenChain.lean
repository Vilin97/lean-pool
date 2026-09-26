/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.DiagramChain

/-!
# Row lengths along single-box extensions

A diagram extending another by a single cell bumps exactly one row
length by one; row lengths are monotone in diagram containment.
-/

@[expose] public section

namespace RS

open Finset

/-- Row lengths are monotone in diagram containment. -/
theorem rowLen_mono {lam mu : YoungDiagram} (hle : lam ≤ mu)
    (i : ℕ) : lam.rowLen i ≤ mu.rowLen i := by
  by_contra h
  have h1 : (i, mu.rowLen i) ∈ lam := by
    rw [YoungDiagram.mem_iff_lt_rowLen]
    omega
  have h2 : (i, mu.rowLen i) ∈ mu := hle h1
  rw [YoungDiagram.mem_iff_lt_rowLen] at h2
  omega

/-- A single-cell extension bumps exactly one row length. -/
theorem rowLen_of_card_succ {lam nu : YoungDiagram}
    (hle : lam ≤ nu) (hcard : nu.card = lam.card + 1) :
    ∃ i₀ : ℕ, ∀ i : ℕ,
      nu.rowLen i = (if i = i₀ then lam.rowLen i + 1
        else lam.rowLen i) := by
  classical
  have hsub : lam.cells ⊆ nu.cells :=
    YoungDiagram.cells_subset_iff.mpr hle
  have hss : lam.cells ⊂ nu.cells := by
    refine ⟨hsub, fun hrev => ?_⟩
    have : nu.card = lam.card :=
      le_antisymm (Finset.card_le_card hrev)
        (Finset.card_le_card hsub)
    omega
  obtain ⟨c, hc_notin, hc_ins⟩ :=
    Finset.ssubset_iff.mp hss
  have hcells : nu.cells = insert c lam.cells := by
    refine (Finset.eq_of_subset_of_card_le hc_ins ?_).symm
    rw [Finset.card_insert_of_notMem hc_notin]
    change nu.card ≤ lam.card + 1
    omega
  refine ⟨c.1, fun i => ?_⟩
  by_cases hi : i = c.1
  · subst hi
    -- the new cell sits at the end of its row
    have hcmem : c ∈ nu := by
      rw [← YoungDiagram.mem_cells, hcells]
      exact Finset.mem_insert_self c lam.cells
    have hlt : c.2 < nu.rowLen c.1 := by
      rw [← YoungDiagram.mem_iff_lt_rowLen]
      exact (show (c.1, c.2) ∈ nu from hcmem)
    have hnotl : ¬ c.2 < lam.rowLen c.1 := by
      rw [← YoungDiagram.mem_iff_lt_rowLen]
      intro hmem
      exact hc_notin ((YoungDiagram.mem_cells _).mpr hmem)
    have hup : ∀ j : ℕ, j < nu.rowLen c.1 → j ≠ c.2 →
        j < lam.rowLen c.1 := by
      intro j hj hne
      rw [← YoungDiagram.mem_iff_lt_rowLen] at hj ⊢
      have : (c.1, j) ∈ nu.cells :=
        (YoungDiagram.mem_cells _).mpr hj
      rw [hcells, Finset.mem_insert] at this
      rcases this with heq | hmem
      · exact absurd (congrArg Prod.snd heq) hne
      · exact (YoungDiagram.mem_cells _).mp hmem
    rw [ite_eq_left rfl]
    -- rowLen nu = c.2 + 1 and rowLen lam = c.2
    have h1 : c.2 + 1 ≤ nu.rowLen c.1 := hlt
    have h2 : lam.rowLen c.1 ≤ c.2 := by omega
    have h3 : nu.rowLen c.1 ≤ c.2 + 1 := by
      by_contra h
      have := hup (c.2 + 1) (by omega) (by omega)
      omega
    have h4 : c.2 ≤ lam.rowLen c.1 := by
      by_cases hz : c.2 = 0
      · omega
      · have := hup (c.2 - 1) (by omega) (by omega)
        omega
    omega
  · rw [ite_eq_right hi]
    apply le_antisymm
    · by_contra h
      have hmem : (i, lam.rowLen i) ∈ nu := by
        rw [YoungDiagram.mem_iff_lt_rowLen]
        omega
      have : (i, lam.rowLen i) ∈ nu.cells :=
        (YoungDiagram.mem_cells _).mpr hmem
      rw [hcells, Finset.mem_insert] at this
      rcases this with heq | hmem'
      · exact hi (congrArg Prod.fst heq)
      · have := (YoungDiagram.mem_cells _).mp hmem'
        rw [YoungDiagram.mem_iff_lt_rowLen] at this
        omega
    · exact rowLen_mono hle i

end RS
