/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPairing

/-!
# S_d-invariance of the pinned pairing (Lemma 5.1(b))

The pinned tensor-power pairing `betaColour` is invariant under
simultaneous permutation of both colourings' positions.

The key combinatorial fact: with matching parities the crossing
count `koszulCrossings c c'` depends only on `c.oddSet.card`,
via the identity `2 * crossings = n * (n - 1)` (upper/lower
triangle of the off-diagonal). Since permutations preserve
`oddSet.card`, the crossing count — hence the Koszul sign — is
invariant.

The formalization does not consume this lemma: it obtains the
same `S_d`-invariance one level upstream, geometrically, from
`RS.vertexStarClass_perm`, where all legs of a vertex star meet
the same vertex and a permutation bundle map is absorbed before
the fibre functor is applied.  The lemma is kept because it is a
numbered lemma of the paper.
-/

namespace RS

namespace MixedColouring

/-- Permuting a colouring by a permutation of positions. -/
def perm {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d)) : MixedColouring k ℓ d :=
  fun i => c (π i)

/-- Permuting a colouring's positions. -/
@[simp]
theorem perm_apply {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d)) (i : Fin d) :
    (c.perm π) i = c (π i) := rfl

/-- The odd support of a permuted colouring is the image of
the original odd support under `π⁻¹`. -/
theorem oddSet_perm {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d)) :
    (c.perm π).oddSet = c.oddSet.map π.symm.toEmbedding := by
  -- First normalise the decidability instance away from `perm`
  have h0 : (c.perm π).oddSet =
      Finset.univ.filter (fun i : Fin d => (c (π i)).isRight) := by
    unfold oddSet
    exact Finset.filter_congr (fun _ _ => Iff.rfl)
  rw [h0]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨π i, by simp only [oddSet, Finset.mem_filter,
      Finset.mem_univ, true_and]; exact h, π.symm_apply_apply i⟩
  · rintro ⟨j, hj, hji⟩
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    have : π i = j := by rw [← hji]; exact π.apply_symm_apply j
    rwa [this]

/-- Permuting does not change how many positions are odd. -/
theorem oddSet_card_perm {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d)) :
    (c.perm π).oddSet.card = c.oddSet.card := by
  rw [oddSet_perm]; exact Finset.card_map _

end MixedColouring

/-- The product of position form entries is
permutation-invariant. -/
theorem prod_colourFormEntry_perm {k ℓ d : ℕ}
    (c c' : MixedColouring k ℓ d) (π : Equiv.Perm (Fin d)) :
    ∏ i, colourFormEntry k ℓ ((c.perm π) i) ((c'.perm π) i) =
    ∏ i, colourFormEntry k ℓ (c i) (c' i) :=
  Equiv.prod_comp (π : Fin d ≃ Fin d)
    (fun i => colourFormEntry k ℓ (c i) (c' i))

/-! ### Koszul crossing invariance -/

/-- With matching parities, the crossing count uses only the
first colouring's odd positions. -/
private theorem koszulCrossings_eq_of_parity_match {k ℓ d : ℕ}
    {c c' : MixedColouring k ℓ d}
    (hpar : ∀ i, (c i).isRight = (c' i).isRight) :
    koszulCrossings c c' = koszulCrossings c c := by
  unfold koszulCrossings
  congr 1; ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, (hpar i) ▸ h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, (hpar i).symm ▸ h3⟩⟩

/-- The swap map bijects upper-triangle to lower-triangle pairs
in `S ×ˢ S`, so both halves have the same cardinality. -/
private theorem card_filter_lt_eq_card_filter_gt
    {α : Type*} [DecidableEq α] [LinearOrder α]
    (S : Finset α) :
    ((S ×ˢ S).filter (fun p : α × α => p.1 < p.2)).card =
    ((S ×ˢ S).filter (fun p : α × α => p.2 < p.1)).card := by
  have h : (S ×ˢ S).filter (fun p : α × α => p.1 < p.2) =
      ((S ×ˢ S).filter (fun p : α × α => p.2 < p.1)).image
        Prod.swap := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product,
      Finset.mem_image, Prod.swap_prod_mk, Prod.exists,
      Prod.mk.injEq]
    constructor
    · intro ⟨⟨ha, hb⟩, hlt⟩
      exact ⟨b, a, ⟨⟨hb, ha⟩, hlt⟩, rfl, rfl⟩
    · rintro ⟨a', b', ⟨⟨ha', hb'⟩, hlt'⟩, rfl, rfl⟩
      exact ⟨⟨hb', ha'⟩, hlt'⟩
  rw [h, Finset.card_image_of_injective _ Prod.swap_injective]

/-- `2 * |{(i,j) ∈ S² | i < j}| = |S|² − |S|`:
the strictly-ordered pairs are exactly half the off-diagonal. -/
private theorem two_mul_strictPairs {α : Type*}
    [DecidableEq α] [LinearOrder α] (S : Finset α) :
    2 * ((S ×ˢ S).filter
      (fun p : α × α => p.1 < p.2)).card =
    S.card * S.card - S.card := by
  have hcompl :
      (S ×ˢ S).filter (fun p : α × α => ¬ p.1 < p.2) =
      (S ×ˢ S).filter (fun p : α × α => p.1 = p.2) ∪
      (S ×ˢ S).filter (fun p : α × α => p.2 < p.1) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product,
      Finset.mem_union, not_lt]
    constructor
    · intro ⟨⟨ha, hb⟩, hle⟩
      rcases hle.eq_or_lt with heq | hlt
      · left; exact ⟨⟨ha, hb⟩, heq.symm⟩
      · right; exact ⟨⟨ha, hb⟩, hlt⟩
    · rintro (⟨⟨ha, hb⟩, heq⟩ | ⟨⟨ha, hb⟩, hlt⟩)
      · exact ⟨⟨ha, hb⟩, le_of_eq heq.symm⟩
      · exact ⟨⟨ha, hb⟩, le_of_lt hlt⟩
  have hd : Disjoint
      ((S ×ˢ S).filter (fun p : α × α => p.1 = p.2))
      ((S ×ˢ S).filter (fun p : α × α => p.2 < p.1)) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, _⟩ _ heq hlt
    exact absurd hlt (not_lt.mpr (le_of_eq heq))
  have hfilt :
      ((S ×ˢ S).filter (fun p : α × α => p.1 < p.2)).card +
      ((S ×ˢ S).filter (fun p : α × α => ¬ p.1 < p.2)).card =
      (S ×ˢ S).card :=
    Finset.card_filter_add_card_filter_not
      (fun p : α × α => p.1 < p.2)
  rw [hcompl, Finset.card_union_of_disjoint hd] at hfilt
  have hswap := card_filter_lt_eq_card_filter_gt S
  have hdiag :
      ((S ×ˢ S).filter
        (fun p : α × α => p.1 = p.2)).card = S.card := by
    have : (S ×ˢ S).filter (fun p : α × α => p.1 = p.2) =
        S.diag := Finset.diag_eq_filter.symm
    rw [this, Finset.diag_card]
  have hprod : (S ×ˢ S).card = S.card * S.card :=
    Finset.card_product S S
  omega

/-- Twice the self-crossing count equals `n² − n` where `n` is
the odd-set cardinality. -/
private theorem two_mul_koszulCrossings_self {k ℓ d : ℕ}
    (c : MixedColouring k ℓ d) :
    2 * koszulCrossings c c =
    c.oddSet.card * c.oddSet.card - c.oddSet.card := by
  have hrel : koszulCrossings c c =
      ((c.oddSet ×ˢ c.oddSet).filter
        (fun p : Fin d × Fin d => p.1 < p.2)).card := by
    unfold koszulCrossings MixedColouring.oddSet
    congr 1; ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product]
    tauto
  rw [hrel]
  exact two_mul_strictPairs c.oddSet

/-- Self-crossings are preserved by permutation. -/
private theorem koszulCrossings_self_perm {k ℓ d : ℕ}
    (c : MixedColouring k ℓ d) (π : Equiv.Perm (Fin d)) :
    koszulCrossings (c.perm π) (c.perm π) =
    koszulCrossings c c := by
  have h1 := two_mul_koszulCrossings_self (c.perm π)
  have h2 := two_mul_koszulCrossings_self c
  rw [MixedColouring.oddSet_card_perm] at h1
  have h3 := h1.trans h2.symm
  omega

/-- Crossings are preserved by permutation when parities
match. -/
private theorem koszulCrossings_perm {k ℓ d : ℕ}
    (c c' : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d))
    (hpar : ∀ i, (c i).isRight = (c' i).isRight) :
    koszulCrossings (c.perm π) (c'.perm π) =
    koszulCrossings c c' := by
  rw [koszulCrossings_eq_of_parity_match (fun i => by
      simp only [MixedColouring.perm_apply]
      exact hpar (π i)),
    koszulCrossings_eq_of_parity_match hpar,
    koszulCrossings_self_perm]

/-- **Lemma 5.1(b)**: the pinned pairing is S_d-invariant on
the support (matching parities). -/
theorem betaColour_perm {k ℓ d : ℕ} (π : Equiv.Perm (Fin d))
    (c c' : MixedColouring k ℓ d)
    (hpar : ∀ i, (c i).isRight = (c' i).isRight) :
    betaColour (c.perm π) (c'.perm π) = betaColour c c' := by
  unfold betaColour
  congr 1
  · congr 1; exact koszulCrossings_perm c c' π hpar
  · exact prod_colourFormEntry_perm c c' π

/-- **Lemma 5.1(b), unconditional**: the pinned pairing is
S_d-invariant. Off the support both sides vanish. -/
theorem betaColour_perm' {k ℓ d : ℕ} (π : Equiv.Perm (Fin d))
    (c c' : MixedColouring k ℓ d) :
    betaColour (c.perm π) (c'.perm π) = betaColour c c' := by
  by_cases hpar : ∀ i, (c i).isRight = (c' i).isRight
  · exact betaColour_perm π c c' hpar
  · push Not at hpar
    obtain ⟨i, hi⟩ := hpar
    have hmix : betaColour c c' = 0 :=
      betaColour_eq_zero_of_mixed i hi
    have hmix' : betaColour (c.perm π) (c'.perm π) = 0 := by
      apply betaColour_eq_zero_of_mixed (π.symm i)
      simp only [MixedColouring.perm_apply,
        Equiv.apply_symm_apply]
      exact hi
    rw [hmix, hmix']

end RS
