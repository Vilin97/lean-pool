/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ActualCellularBoundary
import Mathlib.Data.Fintype.Sort
/-!
# Facet extensions and shuffles

For a codimension-one Fox--Neuwirth cell, the labels form two ordered blocks. A containing top
cell is exactly an order-preserving interleaving of these blocks, hence is determined by the set
of positions occupied by the first block. This module constructs the inverse interleaving,
proves the resulting equivalence with `ShuffleIndex`, and closes the genuine cellular-cycle
calculation modulo a prime.
-/

namespace NRR

variable {p : Nat}

namespace FoxNeuwirth

/-- A codimension-one facet has two blocks; this equivalence records the old rank inside the
left or right block. -/
noncomputable def facetLabelSumEquiv
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    Fin p ≃
      (Fin (facetLeftSize hp a ha) ⊕
        Fin (p - facetLeftSize hp a ha)) where
  toFun i :=
    if hi : (a.rank i).1 < facetLeftSize hp a ha then
      Sum.inl ⟨(a.rank i).1, hi⟩
    else
      Sum.inr ⟨(a.rank i).1 - facetLeftSize hp a ha, by
        have hirank := (a.rank i).2
        have hk := facetLeftSize_lt hp a ha
        omega⟩
  invFun x :=
    match x with
    | Sum.inl i =>
        a.rank.symm ⟨i.1, lt_trans i.2 (facetLeftSize_lt hp a ha)⟩
    | Sum.inr i =>
        a.rank.symm ⟨facetLeftSize hp a ha + i.1, by
          have hi := i.2
          omega⟩
  left_inv i := by
    dsimp
    split_ifs with hi
    · simp
    · have hge : facetLeftSize hp a ha ≤ (a.rank i).1 := Nat.le_of_not_gt hi
      simpa [Nat.add_sub_of_le hge]
  right_inv x := by
    rcases x with i | i
    · dsimp
      simp
    · dsimp
      have hnot : ¬ facetLeftSize hp a ha + i.1 < facetLeftSize hp a ha := by omega
      simp [hnot]

/-- The complement of a shuffle has the complementary cardinality. -/
theorem shuffle_compl_card
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha)) :
    s.1ᶜ.card = p - facetLeftSize hp a ha := by
  rw [Finset.card_compl]
  simpa [s.2]

/-- Increasing merge of the two ordered blocks into the positions selected by a shuffle. -/
noncomputable def shuffleMergeEquiv
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha)) :
    (Fin (facetLeftSize hp a ha) ⊕
      Fin (p - facetLeftSize hp a ha)) ≃ Fin p :=
  finSumEquivOfFinset s.2 (shuffle_compl_card hp a ha s)

/-- The top-cell rank obtained by interleaving the two ordered blocks according to `s`. -/
noncomputable def shuffleRank
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha)) :
    Equiv.Perm (Fin p) :=
  (facetLabelSumEquiv hp a ha).trans (shuffleMergeEquiv hp a ha s)

/-- On a first-block label, `shuffleRank` is the increasing enumeration of the selected positions. -/
theorem shuffleRank_apply_left
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha))
    (i : Fin p) (hi : (a.rank i).1 < facetLeftSize hp a ha) :
    shuffleRank hp a ha s i =
      s.1.orderEmbOfFin s.2 ⟨(a.rank i).1, hi⟩ := by
  simp [shuffleRank, facetLabelSumEquiv, shuffleMergeEquiv, hi,
    finSumEquivOfFinset_inl]

/-- On a second-block label, `shuffleRank` is the increasing enumeration of the complementary
positions. -/
theorem shuffleRank_apply_right
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha))
    (i : Fin p) (hi : ¬ (a.rank i).1 < facetLeftSize hp a ha) :
    shuffleRank hp a ha s i =
      s.1ᶜ.orderEmbOfFin (shuffle_compl_card hp a ha s)
        ⟨(a.rank i).1 - facetLeftSize hp a ha, by
          have _hirank := (a.rank i).2
          have hk := facetLeftSize_lt hp a ha
          omega⟩ := by
  simp [shuffleRank, facetLabelSumEquiv, shuffleMergeEquiv, hi,
    finSumEquivOfFinset_inr]

/-- In a codimension-one cell, two labels are in the same block exactly when their old ranks lie
on the same side of the unique bar. -/
theorem sameBlock_iff_same_side
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) (i j : Fin p) :
    a.SameBlock i j ↔
      ((a.rank i).1 < facetLeftSize hp a ha ↔
        (a.rank j).1 < facetLeftSize hp a ha) := by
  unfold BarredPermutation.SameBlock BarredPermutation.blockIndex
  rw [bars_eq_singleton_facetBar hp a ha]
  by_cases hi : (facetBar hp a ha).1 < (a.rank i).1
  <;> by_cases hj : (facetBar hp a ha).1 < (a.rank j).1
  <;> simp [hi, hj, facetLeftSize, Finset.filter_singleton,
       Finset.card_singleton, Finset.card_empty]
  <;> omega

/-- The shuffle merge preserves the old order inside each of the two facet blocks. -/
theorem shuffleRank_preserves_sameBlock_order
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha))
    (i j : Fin p) (hij : a.SameBlock i j) :
    ((a.rank i).1 < (a.rank j).1 ↔
      (shuffleRank hp a ha s i).1 < (shuffleRank hp a ha s j).1) := by
  have hside := (sameBlock_iff_same_side hp a ha i j).1 hij
  by_cases hi : (a.rank i).1 < facetLeftSize hp a ha
  · have hj : (a.rank j).1 < facetLeftSize hp a ha := hside.mp hi
    rw [shuffleRank_apply_left hp a ha s i hi,
      shuffleRank_apply_left hp a ha s j hj]
    simp
  · have hj : ¬ (a.rank j).1 < facetLeftSize hp a ha := by
      intro hj
      exact hi (hside.mpr hj)
    rw [shuffleRank_apply_right hp a ha s i hi,
      shuffleRank_apply_right hp a ha s j hj]
    simp
    omega

/-- The merged permutation is a top-cell extension of the original facet. -/
theorem shuffleTopCell_isFacet
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha)) :
    a.IsFacet
      ((BarredPermutation.TopCell.ofPerm (shuffleRank hp a ha s) :
        BarredPermutation.TopCell p) : BarredPermutation p) := by
  let c : BarredPermutation.TopCell p :=
    BarredPermutation.TopCell.ofPerm (shuffleRank hp a ha s)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      change 0 ≤ 0
      exact le_rfl
    · intro i j hij
      simpa [c] using shuffleRank_preserves_sameBlock_order hp a ha s i j hij
    · rw [ha, BarredPermutation.TopCell.dimension hp c]
      omega
  · rw [ha, BarredPermutation.TopCell.dimension hp c]
    have := hp.two_le
    omega

/-- Inverse construction: merge the two ordered blocks according to the chosen shuffle. -/
noncomputable def shuffleToTopExtension
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    ShuffleIndex p (facetLeftSize hp a ha) → TopExtension a :=
  fun s =>
    ⟨BarredPermutation.TopCell.ofPerm (shuffleRank hp a ha s),
      shuffleTopCell_isFacet hp a ha s⟩

/-- The first-block positions of the constructed extension are the prescribed shuffle. -/
theorem firstBlockPositions_shuffleToTopExtension
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha)) :
    firstBlockPositions hp a ha (shuffleToTopExtension hp a ha s).1 = s.1 := by
  unfold firstBlockPositions
  -- The TopCell.rank equals shuffleRank
  simp [shuffleToTopExtension, BarredPermutation.TopCell.ofPerm_rank]
  -- Use shuffleRank_apply_left to rewrite the image
  have himage : Finset.image (fun i : FirstBlockLabel hp a ha =>
      shuffleRank hp a ha s i.1) Finset.univ =
    Finset.image (fun j : Fin (facetLeftSize hp a ha) =>
      s.1.orderEmbOfFin s.2 j) Finset.univ := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨(a.rank i.1).1, i.2⟩, (shuffleRank_apply_left hp a ha s i.1 i.2).symm⟩
    · rintro ⟨j, rfl⟩
      let i := (firstBlockEquivFin hp a ha).symm j
      use i
      rw [shuffleRank_apply_left hp a ha s i.1 i.2]
      change s.1.orderEmbOfFin s.2 ((firstBlockEquivFin hp a ha) i) = _
      rw [(firstBlockEquivFin hp a ha).apply_symm_apply j]
  have hcard : Fintype.card (Fin (facetLeftSize hp a ha)) = s.1.card := by
    simpa using s.2.symm
  have hfinal : Finset.image (fun j : Fin (facetLeftSize hp a ha) =>
      s.1.orderEmbOfFin s.2 j) Finset.univ = s.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := hx
      exact s.1.orderEmbOfFin_mem s.2 j
    · simp []
  exact himage.trans hfinal

@[simp] theorem topExtensionToShuffle_shuffleToTopExtension
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha)) :
    topExtensionToShuffle hp a ha (shuffleToTopExtension hp a ha s) = s := by
  apply Subtype.ext
  exact firstBlockPositions_shuffleToTopExtension hp a ha s

/-- A top-cell extension is order-preserving on each facet block. -/
theorem topExtension_preserves_sameBlock_order
    (a : BarredPermutation p) (c : TopExtension a)
    (i j : Fin p) (hij : a.SameBlock i j) :
    ((a.rank i).1 < (a.rank j).1 ↔
      (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i).1 <
        (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank j).1) :=
  c.2.1.2.1 i j hij

/-- A label occupies a first-block position in an extension exactly when it belongs to the first
block of the facet. -/
theorem rank_mem_firstBlockPositions_iff
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) (i : Fin p) :
    ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i ∈
        firstBlockPositions hp a ha c.1 ↔
      (a.rank i).1 < facetLeftSize hp a ha := by
  classical
  rw [firstBlockPositions, Finset.mem_image]
  constructor
  · rintro ⟨j, -, hji⟩
    have hlabels : j.1 = i :=
      (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank.injective hji)
    simpa [hlabels] using j.2
  · intro hi
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

/-- The first-block restriction of a top-cell extension, indexed by old rank. -/
noncomputable def topExtensionLeftOrderEmb
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) :
    Fin (facetLeftSize hp a ha) ↪o Fin p where
  toFun r :=
    ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank
      (a.rank.symm ⟨r.1, lt_trans r.2 (facetLeftSize_lt hp a ha)⟩)
  inj' := by
    intro r s hrs
    have heq := (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank.injective hrs)
    have := congr_arg a.rank heq
    simp at this
    exact Fin.ext this
  map_rel_iff' := by
    intro r₁ r₂
    simp only [Fin.le_def]
    let i₁ := a.rank.symm ⟨r₁.1, lt_trans r₁.2 (facetLeftSize_lt hp a ha)⟩
    let i₂ := a.rank.symm ⟨r₂.1, lt_trans r₂.2 (facetLeftSize_lt hp a ha)⟩
    have hi₁ : (a.rank i₁).1 = r₁.1 := by simp [i₁]
    have hi₂ : (a.rank i₂).1 = r₂.1 := by simp [i₂]
    have hs : a.SameBlock i₁ i₂ := by
      rw [sameBlock_iff_same_side hp a ha]
      simp [hi₁, hi₂]
    have hpso := topExtension_preserves_sameBlock_order a c i₁ i₂ hs
    simp only [hi₁, hi₂] at hpso
    change ((c.1 : BarredPermutation p).rank i₁).1 ≤ ((c.1 : BarredPermutation p).rank i₂).1 ↔ r₁.1 ≤ r₂.1
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hpso]
    have heq : ((c.1 : BarredPermutation p).rank i₁).1 = ((c.1 : BarredPermutation p).rank i₂).1 ↔ r₁.1 = r₂.1 := by
      have injc : Function.Injective ((c.1 : BarredPermutation p).rank) := ((c.1 : BarredPermutation p).rank).injective
      constructor
      · intro h
        have heq1 : (c.1 : BarredPermutation p).rank i₁ = (c.1 : BarredPermutation p).rank i₂ := Fin.ext h
        have heq2 : i₁ = i₂ := injc heq1
        rw [← hi₁, ← hi₂, heq2]
      · intro h
        have heq1 : r₁ = r₂ := Fin.ext h
        have heq2 : i₁ = i₂ := congrArg (fun r => a.rank.symm ⟨r.1, lt_trans r.2 (facetLeftSize_lt hp a ha)⟩) heq1
        simp [heq2]
    rw [heq]

/-- The first-block restriction lands in the first-block position finset. -/
theorem topExtensionLeftOrderEmb_mem
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) (r : Fin (facetLeftSize hp a ha)) :
    topExtensionLeftOrderEmb hp a ha c r ∈ firstBlockPositions hp a ha c.1 := by
  apply (rank_mem_firstBlockPositions_iff hp a ha c _).2
  simp []

/-- The increasing enumeration of first-block positions agrees with every top-cell extension. -/
theorem topExtension_left_rank_eq_orderEmb
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) (i : Fin p)
    (hi : (a.rank i).1 < facetLeftSize hp a ha) :
    ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i =
      (firstBlockPositions hp a ha c.1).orderEmbOfFin
        (card_firstBlockPositions hp a ha c.1)
        ⟨(a.rank i).1, hi⟩ := by
  have hemb :
      topExtensionLeftOrderEmb hp a ha c =
        (firstBlockPositions hp a ha c.1).orderEmbOfFin
          (card_firstBlockPositions hp a ha c.1) :=
    Finset.orderEmbOfFin_unique'
      (card_firstBlockPositions hp a ha c.1)
      (topExtensionLeftOrderEmb_mem hp a ha c)
  have happ := congrArg (fun e => e ⟨(a.rank i).1, hi⟩) hemb
  have hlabel :
      a.rank.symm ⟨(a.rank i).1, lt_trans hi (facetLeftSize_lt hp a ha)⟩ = i := by
    apply a.rank.injective
    apply Fin.ext
    simp
  change ((c.1 : BarredPermutation p).rank
      (a.rank.symm ⟨(a.rank i).1, lt_trans hi (facetLeftSize_lt hp a ha)⟩)) = _ at happ
  rw [hlabel] at happ
  exact happ

/-- The complement of the first-block position set has the size of the second block. -/
theorem card_compl_firstBlockPositions
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) :
    (firstBlockPositions hp a ha c.1)ᶜ.card =
      p - facetLeftSize hp a ha := by
  rw [Finset.card_compl, card_firstBlockPositions hp a ha c.1, Fintype.card_fin]

/-- The second-block restriction of a top-cell extension, indexed by old rank within that block. -/
noncomputable def topExtensionRightOrderEmb
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) :
    Fin (p - facetLeftSize hp a ha) ↪o Fin p where
  toFun r :=
    ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank
      (a.rank.symm ⟨facetLeftSize hp a ha + r.1, by
        have hr := r.2
        have hk := facetLeftSize_lt hp a ha
        omega⟩)
  inj' := by
    intro r₁ r₂ h
    have h1 := (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank.injective h)
    have h2 := a.rank.symm.injective h1
    exact Fin.ext (by simp at h2; omega)
  map_rel_iff' := by
    intro r₁ r₂
    have h₁ : facetLeftSize hp a ha + r₁.1 < p := by have := r₁.2; omega
    have h₂ : facetLeftSize hp a ha + r₂.1 < p := by have := r₂.2; omega
    have hside₁ : ¬ (facetLeftSize hp a ha + r₁.1) < facetLeftSize hp a ha := by omega
    have hside₂ : ¬ (facetLeftSize hp a ha + r₂.1) < facetLeftSize hp a ha := by omega
    let i₁ := a.rank.symm ⟨facetLeftSize hp a ha + r₁.1, h₁⟩
    let i₂ := a.rank.symm ⟨facetLeftSize hp a ha + r₂.1, h₂⟩
    have hSB : a.SameBlock i₁ i₂ := by
      rw [sameBlock_iff_same_side hp a ha i₁ i₂]
      simp [i₁, i₂, hside₁, hside₂]
    have hpres := topExtension_preserves_sameBlock_order a c i₁ i₂ hSB
    have hrank_i1 : a.rank i₁ = ⟨facetLeftSize hp a ha + r₁.1, h₁⟩ := by simp [i₁]
    have hrank_i2 : a.rank i₂ = ⟨facetLeftSize hp a ha + r₂.1, h₂⟩ := by simp [i₂]
    rw [hrank_i1, hrank_i2] at hpres
    -- hpres : r₁ < r₂ ↔ (c.1.rank i₁) < (c.1.rank i₂)
    -- Goal is about (c.1.rank i₁).1 ≤ (c.1.rank i₂).1 ↔ r₁ ≤ r₂
    rw [Nat.add_lt_add_iff_left] at hpres
    have hpres_le : ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₁ ≤ ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₂ ↔ r₁ ≤ r₂ := by
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | heq
        · left; exact hpres.mpr h
        · right
          have hpres_rev : r₂ < r₁ ↔ (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₂) < (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₁) := by
            rcases lt_trichotomy r₁ r₂ with h | h | h
            · -- r₁ < r₂: both sides of iff are false
              have hc : ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₁ < ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₂ := hpres.mp h
              simp [not_lt.mpr (le_of_lt h), not_lt.mpr (le_of_lt hc)]
            · -- r₁ = r₂: both sides of iff are false
              subst h
              simp [heq]
            · -- r₂ < r₁: both sides of iff are true
              have hnot1 : ¬(r₁ < r₂) := not_lt.mpr (le_of_lt h)
              have hnot2 : ¬(((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₁ <
                             ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₂) := by
                intro hc
                exact hnot1 (hpres.mpr hc)
              have hne : (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₁ ≠
                          ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₂) := by
                intro heq'
                have heq_i : i₁ = i₂ := (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank.injective heq')
                have : r₁ = r₂ := by
                  have := congr_arg a.rank heq_i
                  simp [hrank_i1, hrank_i2] at this
                  exact Fin.ext (by omega)
                exact lt_irrefl _ (h.trans_le (le_of_eq this))
              rcases lt_trichotomy (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₁)
                                  (((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i₂) with h' | h' | h'
              · exact False.elim (hnot2 h')
              · exact False.elim (hne h')
              · exact Iff.intro (fun _ => h') (fun _ => h)
          have h1 : ¬(r₁ < r₂) := fun h' => lt_irrefl _ (heq ▸ (hpres.mp h'))
          have h2 : ¬(r₂ < r₁) := fun h' => lt_irrefl _ (heq.symm ▸ (hpres_rev.mp h'))
          exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      · rcases h with h | heq
        · left; exact hpres.mp h
        · right
          have hi : i₁ = i₂ := by simp [i₁, i₂, heq]
          rw [hi]
    exact hpres_le

/-- The second-block restriction lands in the complementary position finset. -/
theorem topExtensionRightOrderEmb_mem
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) (r : Fin (p - facetLeftSize hp a ha)) :
    topExtensionRightOrderEmb hp a ha c r ∈
      (firstBlockPositions hp a ha c.1)ᶜ := by
  rw [Finset.mem_compl]
  apply (rank_mem_firstBlockPositions_iff hp a ha c _).not.mpr
  simp []

/-- The increasing enumeration of complementary positions agrees with every top-cell extension. -/
theorem topExtension_right_rank_eq_orderEmb
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : TopExtension a) (i : Fin p)
    (hi : ¬ (a.rank i).1 < facetLeftSize hp a ha) :
    ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank i =
      (firstBlockPositions hp a ha c.1)ᶜ.orderEmbOfFin
        (card_compl_firstBlockPositions hp a ha c)
        ⟨(a.rank i).1 - facetLeftSize hp a ha, by
          have _hirank := (a.rank i).2
          have hk := facetLeftSize_lt hp a ha
          omega⟩ := by
  have hemb :
      topExtensionRightOrderEmb hp a ha c =
        (firstBlockPositions hp a ha c.1)ᶜ.orderEmbOfFin
          (card_compl_firstBlockPositions hp a ha c) :=
    Finset.orderEmbOfFin_unique'
      (card_compl_firstBlockPositions hp a ha c)
      (topExtensionRightOrderEmb_mem hp a ha c)
  let r : Fin (p - facetLeftSize hp a ha) :=
    ⟨(a.rank i).1 - facetLeftSize hp a ha, by
      have hirank := (a.rank i).2
      have hk := facetLeftSize_lt hp a ha
      omega⟩
  have happ := congrArg (fun e => e r) hemb
  have hge : facetLeftSize hp a ha ≤ (a.rank i).1 := Nat.le_of_not_gt hi
  have hlabel :
      a.rank.symm ⟨facetLeftSize hp a ha + ((a.rank i).1 - facetLeftSize hp a ha), by
        have hirank := (a.rank i).2
        omega⟩ = i := by
    apply a.rank.injective
    apply Fin.ext
    simp [Nat.add_sub_of_le hge]
  change ((c.1 : BarredPermutation p).rank
      (a.rank.symm ⟨facetLeftSize hp a ha + r.1, by
        have hr := r.2
        omega⟩)) = _ at happ
  dsimp [r] at happ
  rw [hlabel] at happ
  exact happ

/-- Two extensions with the same first-block position set are equal. -/
theorem topExtensionToShuffle_injective
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    Function.Injective (topExtensionToShuffle hp a ha) := by
  have hcomp : ∀ c : TopExtension a,
      shuffleToTopExtension hp a ha (topExtensionToShuffle hp a ha c) = c := by
    intro c
    apply Subtype.ext
    apply BarredPermutation.TopCell.equivPerm.injective
    change shuffleRank hp a ha (topExtensionToShuffle hp a ha c) =
      ((c.1 : BarredPermutation.TopCell p) : BarredPermutation p).rank
    ext i
    by_cases hi : (a.rank i).1 < facetLeftSize hp a ha
    · apply congrArg Fin.val
      exact (shuffleRank_apply_left hp a ha
        (topExtensionToShuffle hp a ha c) i hi).trans
        (topExtension_left_rank_eq_orderEmb hp a ha c i hi).symm
    · apply congrArg Fin.val
      exact (shuffleRank_apply_right hp a ha
        (topExtensionToShuffle hp a ha c) i hi).trans
        (topExtension_right_rank_eq_orderEmb hp a ha c i hi).symm
  intro c c' h
  rw [← hcomp c, ← hcomp c', congrArg (shuffleToTopExtension hp a ha) h]

/-- Every shuffle is realized by its canonical order-preserving merge. -/
theorem topExtensionToShuffle_surjective
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    Function.Surjective (topExtensionToShuffle hp a ha) := by
  intro s
  exact ⟨shuffleToTopExtension hp a ha s,
    topExtensionToShuffle_shuffleToTopExtension hp a ha s⟩

/-- Canonical equivalence between top-cell extensions of a facet and its shuffles. -/
noncomputable def facetShuffleEquiv
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    TopExtension a ≃ ShuffleIndex p (facetLeftSize hp a ha) :=
  Equiv.ofBijective (topExtensionToShuffle hp a ha)
    ⟨topExtensionToShuffle_injective hp a ha,
      topExtensionToShuffle_surjective hp a ha⟩

/-- The canonical extension-to-shuffle map is bijective. -/
theorem facetShuffleBijection (hp : Nat.Prime p) : FacetShuffleBijection hp := by
  intro a ha
  exact (facetShuffleEquiv hp a ha).bijective

/-- Unconditional shuffle-cardinality formula for all prime facets. -/
theorem facetShuffleCardinality (hp : Nat.Prime p) : FacetShuffleCardinality p :=
  facetShuffleCardinality_of_bijection hp (facetShuffleBijection hp)

/-- Every actual cellular boundary coefficient vanishes modulo the prime. -/
theorem actualTopBoundaryCoefficient_eq_zero_prime
    (hp : Nat.Prime p) (a : BarredPermutation p) :
    actualTopBoundaryCoefficient a = 0 :=
  actualTopBoundaryCoefficient_eq_zero hp (facetShuffleCardinality hp) a

/-- The genuine top-cell incidence sum is an unconditional finite cycle modulo a prime. -/
noncomputable def primeActualFiniteIncidenceCycle
    (hp : Nat.Prime p) : FiniteIncidenceCycle (ZMod p) :=
  actualFiniteIncidenceCycle hp (facetShuffleCardinality hp)

end FoxNeuwirth

end NRR
