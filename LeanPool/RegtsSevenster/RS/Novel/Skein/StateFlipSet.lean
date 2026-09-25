/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TwoPathNonSep

/-!
# Set-indexed state relabels

The odd-partner relabel over a finite set of labels: the ambient
algebra of the accumulated state relabels of the canonical route.
Composition is symmetric difference, so pairing-returning
accumulations cancel by parity.
-/

namespace RS



variable {k ℓ : ℕ} {α : Type}

open Classical in
/-- The odd-partner relabel at every label of a finite set. -/
noncomputable def stateOddFlipSet (st : GenBoundaryState k ℓ α)
    (E : Finset α) : GenBoundaryState k ℓ α :=
  fun i => if i ∈ E then Sum.map id (oddPartner ℓ) (st i) else st i

variable {st : GenBoundaryState k ℓ α}

/-- On the relabel set the state entry is `∂`-flipped. -/
theorem stateOddFlipSet_of_mem {E : Finset α} {i : α}
    (h : i ∈ E) :
    stateOddFlipSet st E i = Sum.map id (oddPartner ℓ) (st i) :=
  ite_eq_left h

/-- Off it the state is unchanged. -/
theorem stateOddFlipSet_of_notMem {E : Finset α} {i : α}
    (h : i ∉ E) : stateOddFlipSet st E i = st i :=
  ite_eq_right h

/-- The empty relabel is the identity. -/
theorem stateOddFlipSet_empty :
    stateOddFlipSet st (∅ : Finset α) = st := by
  funext i
  exact ite_eq_right (Finset.notMem_empty i)

/-- The pair relabel is the two-element set relabel. -/
theorem stateOddFlip_eq_flipSet {i₁ i₂ : α} :
    stateOddFlip st i₁ i₂ = stateOddFlipSet st {i₁, i₂} := by
  funext i
  change (if i = i₁ ∨ i = i₂ then Sum.map id (oddPartner ℓ) (st i)
    else st i) = _
  unfold stateOddFlipSet
  by_cases h : i = i₁ ∨ i = i₂
  · rw [ite_eq_left h, ite_eq_left (by
      rcases h with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  · rw [ite_eq_right h, ite_eq_right (by
      intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem'
      · exact h (Or.inl rfl)
      · exact h (Or.inr (Finset.mem_singleton.mp hmem')))]

/-- **Composition is symmetric difference**: two set relabels
compose to the relabel at the symmetric difference — labels hit
twice cancel by the odd-partner involution. -/
theorem stateOddFlipSet_flipSet (E₁ E₂ : Finset α) :
    stateOddFlipSet (stateOddFlipSet st E₁) E₂ =
      stateOddFlipSet st ((E₁ \ E₂) ∪ (E₂ \ E₁)) := by
  funext i
  unfold stateOddFlipSet
  by_cases h1 : i ∈ E₁ <;> by_cases h2 : i ∈ E₂
  · rw [ite_eq_left h2, ite_eq_left h1, ite_eq_right (by
      intro hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact (Finset.mem_sdiff.mp h).2 h2
      · exact (Finset.mem_sdiff.mp h).2 h1)]
    rcases hst : st i with a | c
    · rfl
    · change Sum.inr (oddPartner ℓ (oddPartner ℓ c)) = Sum.inr c
      rw [oddPartner_invol]
  · rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left
      (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, h2⟩))]
  · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left
      (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2, h1⟩))]
  · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by
      intro hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact h1 (Finset.mem_sdiff.mp h).1
      · exact h2 (Finset.mem_sdiff.mp h).1)]

/-- The relabel does not change which labels carry odd colours. -/
theorem stateOddFlipSet_isInr {st : GenBoundaryState k ℓ α}
    {E : Finset α} (i : α) :
    (∃ c, stateOddFlipSet st E i = Sum.inr c) ↔
      ∃ c, st i = Sum.inr c := by
  constructor
  · rintro ⟨c, hc⟩
    by_cases h : i ∈ E
    · rw [stateOddFlipSet_of_mem h] at hc
      rcases hst : st i with a | b
      · rw [hst] at hc
        simp only [Sum.map_inl] at hc
        cases hc
      · exact ⟨b, rfl⟩
    · rw [stateOddFlipSet_of_notMem h] at hc
      exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    by_cases h : i ∈ E
    · refine ⟨oddPartner ℓ c, ?_⟩
      rw [stateOddFlipSet_of_mem h, hc]
      rfl
    · refine ⟨c, ?_⟩
      rw [stateOddFlipSet_of_notMem h]
      exact hc

/-- The boundary-membership constraint survives any set relabel. -/
theorem genBoundarySubsetMatches_stateOddFlipSet {W : Fragment α}
    {s : Finset W.Flag} {st : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W s st) (E : Finset α) :
    genBoundarySubsetMatches W s (stateOddFlipSet st E) :=
  fun i => (hbnd i).trans (stateOddFlipSet_isInr i).symm

end RS
