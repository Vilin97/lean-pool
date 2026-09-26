/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.Defs

/-!
# Prefix-coherence API

Supporting lemmas relating `champBlocks` to `champPrefix`/`champDigit`:
`champBlocks` is
prefix-monotone in `N`, so `champBlocks_getElem` shows any sufficiently
long block computes the same digit as `champDigit`, and `champPrefix`
(the first `n` digits) agrees with mapping `champDigit` over
`List.range n`. Used by `Positions.lean`, `Asymptotics.lean`, and
`Main.lean`'s proof; not needed to state `champernowne_normal` itself
(see `Defs.lean`).
-/

@[expose] public section

namespace Champernowne

theorem champBlocks_prefix {b N M : ℕ} (h : N ≤ M) :
    champBlocks b N <+: champBlocks b M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [champBlocks, List.range_add, List.map_append, List.flatten_append]
  exact List.prefix_append _ _

/-- Coherence: any sufficiently long prefix computes `champDigit`. -/
theorem champBlocks_getElem (b N i : ℕ) (h : i < (champBlocks b N).length) :
    (champBlocks b N)[i] = champDigit b i := by
  simp only [champDigit]
  rcases le_total N (i + 1) with hN | hN
  · exact (champBlocks_prefix hN).getElem h
  · exact ((champBlocks_prefix hN).getElem (lt_of_lt_of_le (Nat.lt_succ_self i)
      (le_length_champBlocks b (i + 1)))).symm

/-- The first `n` digits of the base-`b` Champernowne sequence. -/
def champPrefix (b n : ℕ) : List ℕ := (champBlocks b n).take n

theorem length_champPrefix (b n : ℕ) : (champPrefix b n).length = n := by
  rw [champPrefix, List.length_take]
  exact Nat.min_eq_left (le_length_champBlocks b n)

theorem champPrefix_eq_map (b n : ℕ) :
    champPrefix b n = (List.range n).map (champDigit b) := by
  have hlen := length_champPrefix b n
  apply List.ext_getElem
  · rw [hlen, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < (champBlocks b n).length := by
      rw [hlen] at h1
      exact lt_of_lt_of_le h1 (le_length_champBlocks b n)
    simp only [champPrefix, List.getElem_take, List.getElem_map, List.getElem_range]
    exact champBlocks_getElem b n i hi

end Champernowne
